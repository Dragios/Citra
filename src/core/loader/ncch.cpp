// Copyright 2014 Citra Emulator Project
// Licensed under GPLv2 or any later version
// Refer to the license.txt file included.

#include <algorithm>
#include <cinttypes>
#include <cstring>
#include <memory>
#include <cryptopp/aes.h>
#include <cryptopp/filters.h>
#include <cryptopp/modes.h>
#include <cryptopp/rsa.h>
#include <cryptopp/sha.h>
#include "common/logging/log.h"
#include "common/string_util.h"
#include "common/swap.h"
#include "core/core.h"
#include "core/file_sys/archive_selfncch.h"
#include "core/hle/kernel/process.h"
#include "core/hle/kernel/resource_limit.h"
#include "core/hle/service/cfg/cfg.h"
#include "core/hle/service/fs/archive.h"
#include "core/hw/aes/key.h"
#include "core/loader/ncch.h"
#include "core/loader/smdh.h"
#include "core/memory.h"

////////////////////////////////////////////////////////////////////////////////////////////////////
// Loader namespace

namespace Loader {

static const int kMaxSections = 8;   ///< Maximum number of sections (files) in an ExeFs
static const int kBlockSize = 0x200; ///< Size of ExeFS blocks (in bytes)

/**
 * Get the decompressed size of an LZSS compressed ExeFS file
 * @param buffer Buffer of compressed file
 * @param size Size of compressed buffer
 * @return Size of decompressed buffer
 */
static u32 LZSS_GetDecompressedSize(const u8* buffer, u32 size) {
    u32 offset_size = *(u32*)(buffer + size - 4);
    return offset_size + size;
}

/**
 * Decompress ExeFS file (compressed with LZSS)
 * @param compressed Compressed buffer
 * @param compressed_size Size of compressed buffer
 * @param decompressed Decompressed buffer
 * @param decompressed_size Size of decompressed buffer
 * @return True on success, otherwise false
 */
static bool LZSS_Decompress(const u8* compressed, u32 compressed_size, u8* decompressed,
                            u32 decompressed_size) {
    const u8* footer = compressed + compressed_size - 8;
    u32 buffer_top_and_bottom = *reinterpret_cast<const u32*>(footer);
    u32 out = decompressed_size;
    u32 index = compressed_size - ((buffer_top_and_bottom >> 24) & 0xFF);
    u32 stop_index = compressed_size - (buffer_top_and_bottom & 0xFFFFFF);

    memset(decompressed, 0, decompressed_size);
    memcpy(decompressed, compressed, compressed_size);

    while (index > stop_index) {
        u8 control = compressed[--index];

        for (unsigned i = 0; i < 8; i++) {
            if (index <= stop_index)
                break;
            if (index <= 0)
                break;
            if (out <= 0)
                break;

            if (control & 0x80) {
                // Check if compression is out of bounds
                if (index < 2)
                    return false;
                index -= 2;

                u32 segment_offset = compressed[index] | (compressed[index + 1] << 8);
                u32 segment_size = ((segment_offset >> 12) & 15) + 3;
                segment_offset &= 0x0FFF;
                segment_offset += 2;

                // Check if compression is out of bounds
                if (out < segment_size)
                    return false;

                for (unsigned j = 0; j < segment_size; j++) {
                    // Check if compression is out of bounds
                    if (out + segment_offset >= decompressed_size)
                        return false;

                    u8 data = decompressed[out + segment_offset];
                    decompressed[--out] = data;
                }
            } else {
                // Check if compression is out of bounds
                if (out < 1)
                    return false;
                decompressed[--out] = compressed[--index];
            }
            control <<= 1;
        }
    }
    return true;
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// AppLoader_NCCH class

FileType AppLoader_NCCH::IdentifyType(FileUtil::IOFile& file) {
    u32 magic;
    file.Seek(0x100, SEEK_SET);
    if (1 != file.ReadArray<u32>(&magic, 1))
        return FileType::Error;

    if (MakeMagic('N', 'C', 'S', 'D') == magic)
        return FileType::CCI;

    if (MakeMagic('N', 'C', 'C', 'H') == magic)
        return FileType::CXI;

    return FileType::Error;
}

std::pair<boost::optional<u32>, ResultStatus> AppLoader_NCCH::LoadKernelSystemMode() {
    if (!is_loaded) {
        ResultStatus res = LoadExeFS();
        if (res != ResultStatus::Success) {
            return std::make_pair(boost::none, res);
        }
    }
    // Set the system mode as the one from the exheader.
    return std::make_pair(exheader_header.arm11_system_local_caps.system_mode.Value(),
                          ResultStatus::Success);
}

ResultStatus AppLoader_NCCH::LoadExec() {
    using Kernel::SharedPtr;
    using Kernel::CodeSet;

    if (!is_loaded)
        return ResultStatus::ErrorNotLoaded;

    std::vector<u8> code;
    if (ResultStatus::Success == ReadCode(code)) {
        std::string process_name = Common::StringFromFixedZeroTerminatedBuffer(
            (const char*)exheader_header.codeset_info.name, 8);

        SharedPtr<CodeSet> codeset = CodeSet::Create(process_name, ncch_header.program_id);

        codeset->code.offset = 0;
        codeset->code.addr = exheader_header.codeset_info.text.address;
        codeset->code.size = exheader_header.codeset_info.text.num_max_pages * Memory::PAGE_SIZE;

        codeset->rodata.offset = codeset->code.offset + codeset->code.size;
        codeset->rodata.addr = exheader_header.codeset_info.ro.address;
        codeset->rodata.size = exheader_header.codeset_info.ro.num_max_pages * Memory::PAGE_SIZE;

        // TODO(yuriks): Not sure if the bss size is added to the page-aligned .data size or just
        //               to the regular size. Playing it safe for now.
        u32 bss_page_size = (exheader_header.codeset_info.bss_size + 0xFFF) & ~0xFFF;
        code.resize(code.size() + bss_page_size, 0);

        codeset->data.offset = codeset->rodata.offset + codeset->rodata.size;
        codeset->data.addr = exheader_header.codeset_info.data.address;
        codeset->data.size =
            exheader_header.codeset_info.data.num_max_pages * Memory::PAGE_SIZE + bss_page_size;

        codeset->entrypoint = codeset->code.addr;
        codeset->memory = std::make_shared<std::vector<u8>>(std::move(code));

        Kernel::g_current_process = Kernel::Process::Create(std::move(codeset));

        // Attach a resource limit to the process based on the resource limit category
        Kernel::g_current_process->resource_limit =
            Kernel::ResourceLimit::GetForCategory(static_cast<Kernel::ResourceLimitCategory>(
                exheader_header.arm11_system_local_caps.resource_limit_category));

        // Set the default CPU core for this process
        Kernel::g_current_process->ideal_processor =
            exheader_header.arm11_system_local_caps.ideal_processor;

        // Copy data while converting endianness
        std::array<u32, ARRAY_SIZE(exheader_header.arm11_kernel_caps.descriptors)> kernel_caps;
        std::copy_n(exheader_header.arm11_kernel_caps.descriptors, kernel_caps.size(),
                    begin(kernel_caps));
        Kernel::g_current_process->ParseKernelCaps(kernel_caps.data(), kernel_caps.size());

        s32 priority = exheader_header.arm11_system_local_caps.priority;
        u32 stack_size = exheader_header.codeset_info.stack_size;
        Kernel::g_current_process->Run(priority, stack_size);
        return ResultStatus::Success;
    }
    return ResultStatus::Error;
}

ResultStatus AppLoader_NCCH::LoadSectionExeFS(const char* name, std::vector<u8>& buffer) {
    if (!file.IsOpen())
        return ResultStatus::Error;

    ResultStatus result = LoadExeFS();
    if (result != ResultStatus::Success)
        return result;

    LOG_DEBUG(Loader, "%d sections:", kMaxSections);
    // Iterate through the ExeFs archive until we find a section with the specified name...
    for (unsigned section_number = 0; section_number < kMaxSections; section_number++) {
        const auto& section = exefs_header.section[section_number];

        // Load the specified section...
        if (strcmp(section.name, name) == 0) {
            LOG_DEBUG(Loader, "%d - offset: 0x%08X, size: 0x%08X, name: %s", section_number,
                      section.offset, section.size, section.name);

            s64 section_offset =
                (section.offset + exefs_offset + sizeof(ExeFs_Header) + ncch_offset);
            file.Seek(section_offset, SEEK_SET);

            if (strcmp(section.name, ".code") == 0 && is_compressed) {
                // Section is compressed, read compressed .code section...
                std::unique_ptr<u8[]> temp_buffer;
                try {
                    temp_buffer.reset(new u8[section.size]);
                } catch (std::bad_alloc&) {
                    return ResultStatus::ErrorMemoryAllocationFailed;
                }

                if (file.ReadBytes(&temp_buffer[0], section.size) != section.size)
                    return ResultStatus::Error;

                if (exerfs_code_aes) {
                    CryptoPP::CTR_Mode<CryptoPP::AES>::Decryption dec;
                    dec.SetKeyWithIV((byte*)exerfs_code_aes->key.data(), 16,
                                     (byte*)exerfs_code_aes->ctr.data(), 16);
                    dec.Seek(section.offset + sizeof(ExeFs_Header));
                    dec.ProcessData((byte*)temp_buffer.get(), (byte*)temp_buffer.get(),
                                    section.size);
                }

                // Decompress .code section...
                u32 decompressed_size = LZSS_GetDecompressedSize(&temp_buffer[0], section.size);
                buffer.resize(decompressed_size);
                if (!LZSS_Decompress(&temp_buffer[0], section.size, &buffer[0], decompressed_size))
                    return ResultStatus::ErrorInvalidFormat;
            } else {
                // Section is uncompressed...
                buffer.resize(section.size);
                if (file.ReadBytes(&buffer[0], section.size) != section.size)
                    return ResultStatus::Error;

                auto aes = strcmp(section.name, ".code") == 0 ? exerfs_code_aes : exefs_aes;
                if (aes) {
                    CryptoPP::CTR_Mode<CryptoPP::AES>::Decryption dec;
                    dec.SetKeyWithIV((byte*)aes->key.data(), 16, (byte*)aes->ctr.data(), 16);
                    dec.Seek(section.offset + sizeof(ExeFs_Header));
                    dec.ProcessData((byte*)buffer.data(), (byte*)buffer.data(), section.size);
                }
            }
            return ResultStatus::Success;
        }
    }
    return ResultStatus::ErrorNotUsed;
}

ResultStatus AppLoader_NCCH::LoadExeFS() {
    if (is_exefs_loaded)
        return ResultStatus::Success;

    if (!file.IsOpen())
        return ResultStatus::Error;

    // Reset read pointer in case this file has been read before.
    file.Seek(0, SEEK_SET);

    if (file.ReadBytes(&ncch_header, sizeof(NCCH_Header)) != sizeof(NCCH_Header))
        return ResultStatus::Error;

    // Skip NCSD header and load first NCCH (NCSD is just a container of NCCH files)...
    if (MakeMagic('N', 'C', 'S', 'D') == ncch_header.magic) {
        LOG_DEBUG(Loader, "Only loading the first (bootable) NCCH within the NCSD file!");
        ncch_offset = 0x4000;
        file.Seek(ncch_offset, SEEK_SET);
        file.ReadBytes(&ncch_header, sizeof(NCCH_Header));
    }

    // Verify we are loading the correct file type...
    if (MakeMagic('N', 'C', 'C', 'H') != ncch_header.magic)
        return ResultStatus::ErrorInvalidFormat;

    // Read ExHeader...

    if (file.ReadBytes(&exheader_header, sizeof(ExHeader_Header)) != sizeof(ExHeader_Header))
        return ResultStatus::Error;

    if (exheader_header.arm11_system_local_caps.program_id != ncch_header.program_id) {
        LOG_INFO(Loader, "The ROM is probably encrypted. Trying to decrypt...");

        AesContext exheader_aes{{}, {}};
        if (ncch_header.version == 0 || ncch_header.version == 2) {
            LOG_INFO(Loader, "NCCH version 0/2");
            std::reverse_copy(ncch_header.partition_id, ncch_header.partition_id + 8,
                              exheader_aes.ctr.begin());
            exefs_aes = exerfs_code_aes = romfs_aes = exheader_aes;
            exheader_aes.ctr[8] = 1;
            exefs_aes->ctr[8] = exerfs_code_aes->ctr[8] = 2;
            romfs_aes->ctr[8] = 3;
        } else if (ncch_header.version == 1) {
            LOG_INFO(Loader, "MCCH version 1");
            std::copy(ncch_header.partition_id, ncch_header.partition_id + 8,
                      exheader_aes.ctr.begin());
            exefs_aes = romfs_aes = exheader_aes;
            auto u32ToBEArray = [](u32 value) -> std::array<u8, 4> {
                return std::array<u8, 4>{(u8)(value >> 24), (u8)((value >> 16) & 0xFF),
                                         (u8)((value >> 8) & 0xFF), (u8)(value & 0xFF)};
            };
            auto offset_exheader = u32ToBEArray(0x200);
            auto offset_exefs = u32ToBEArray(ncch_header.exefs_offset * kBlockSize);
            auto offset_romfs = u32ToBEArray(ncch_header.romfs_offset * kBlockSize);
            std::copy(offset_exheader.begin(), offset_exheader.end(),
                      exheader_aes.ctr.begin() + 12);
            std::copy(offset_exefs.begin(), offset_exefs.end(), exefs_aes->ctr.begin() + 12);
            std::copy(offset_romfs.begin(), offset_romfs.end(), romfs_aes->ctr.begin() + 12);
            exerfs_code_aes = exefs_aes;
        } else {
            LOG_ERROR(Loader, "Unknown NCCH version %d !", ncch_header.version);
            return ResultStatus::ErrorEncrypted;
        }

        if (ncch_header.flags[7] & 1) {
            LOG_INFO(Loader, "FixedKey crypto");
            std::array<u8, 16> zeros{};
            exheader_aes.key = exefs_aes->key = exerfs_code_aes->key = romfs_aes->key = zeros;
        } else {
            HW::AES::InitKeys();
            HW::AES::AESKey key_y;
            if (ncch_header.flags[7] & 0x20) {
                LOG_ERROR(Loader, "Seed crypto unsupported!");
                return ResultStatus::ErrorEncrypted;
            }

            std::memcpy(key_y.data(), ncch_header.signature, sizeof(key_y));
            HW::AES::SetKeyY(HW::AES::KeySlotID::NCCH, key_y);

            if (!HW::AES::IsNormalKeyAvailable(HW::AES::KeySlotID::NCCH)) {
                LOG_ERROR(Loader, "slot0x2CKeyX missing! cannot decrypt!");
                return ResultStatus::ErrorEncrypted;
            }

            exheader_aes.key = exefs_aes->key = HW::AES::GetNormalKey(HW::AES::KeySlotID::NCCH);

            switch (ncch_header.flags[3]) {
            case 0:
                LOG_INFO(Loader, "Standard crypto");
                exerfs_code_aes->key = romfs_aes->key = exheader_aes.key;
                break;
            case 1:
                LOG_INFO(Loader, "7x crypto");
                HW::AES::SetKeyY(HW::AES::KeySlotID::NCCH7x, key_y);
                if (!HW::AES::IsNormalKeyAvailable(HW::AES::KeySlotID::NCCH7x)) {
                    LOG_ERROR(Loader, "slot0x25KeyX missing! Cannot decrypt!");
                    return ResultStatus::ErrorEncrypted;
                }
                exerfs_code_aes->key = romfs_aes->key =
                    HW::AES::GetNormalKey(HW::AES::KeySlotID::NCCH7x);
                break;
            case 0x0A:
                LOG_INFO(Loader, "Secure3 crypto");
                HW::AES::SetKeyY(HW::AES::KeySlotID::NCCHSec3, key_y);
                if (!HW::AES::IsNormalKeyAvailable(HW::AES::KeySlotID::NCCHSec3)) {
                    LOG_ERROR(Loader, "slot0x18KeyX missing! Cannot decrypt!");
                    return ResultStatus::ErrorEncrypted;
                }
                exerfs_code_aes->key = romfs_aes->key =
                    HW::AES::GetNormalKey(HW::AES::KeySlotID::NCCHSec3);
                break;
            case 0x0B:
                LOG_INFO(Loader, "Secure4 crypto");
                HW::AES::SetKeyY(HW::AES::KeySlotID::NCCHSec4, key_y);
                if (!HW::AES::IsNormalKeyAvailable(HW::AES::KeySlotID::NCCHSec4)) {
                    LOG_ERROR(Loader, "slot0x1BKeyX missing! Cannot decrypt!");
                    return ResultStatus::ErrorEncrypted;
                }
                exerfs_code_aes->key = romfs_aes->key =
                    HW::AES::GetNormalKey(HW::AES::KeySlotID::NCCHSec4);
                break;
            default:
                LOG_ERROR(Loader, "Unknown crypto method! Cannot decrypt!");
                return ResultStatus::ErrorEncrypted;
            }
        }

        // Decrypt ExHeader
        CryptoPP::CTR_Mode<CryptoPP::AES>::Decryption dec;
        dec.SetKeyWithIV((byte*)exheader_aes.key.data(), 16, (byte*)exheader_aes.ctr.data(), 16);
        dec.ProcessData((byte*)&exheader_header, (byte*)&exheader_header, sizeof(exheader_header));

        if (exheader_header.arm11_system_local_caps.program_id != ncch_header.program_id) {
            LOG_ERROR(Loader, "Cannot decrypt!");
            return ResultStatus::ErrorEncrypted;
        }
    }

    is_compressed = (exheader_header.codeset_info.flags.flag & 1) == 1;
    entry_point = exheader_header.codeset_info.text.address;
    code_size = exheader_header.codeset_info.text.code_size;
    stack_size = exheader_header.codeset_info.stack_size;
    bss_size = exheader_header.codeset_info.bss_size;
    core_version = exheader_header.arm11_system_local_caps.core_version;
    priority = exheader_header.arm11_system_local_caps.priority;
    resource_limit_category = exheader_header.arm11_system_local_caps.resource_limit_category;

    LOG_DEBUG(Loader, "Name:                        %s", exheader_header.codeset_info.name);
    LOG_DEBUG(Loader, "Program ID:                  %016" PRIX64, ncch_header.program_id);
    LOG_DEBUG(Loader, "Code compressed:             %s", is_compressed ? "yes" : "no");
    LOG_DEBUG(Loader, "Entry point:                 0x%08X", entry_point);
    LOG_DEBUG(Loader, "Code size:                   0x%08X", code_size);
    LOG_DEBUG(Loader, "Stack size:                  0x%08X", stack_size);
    LOG_DEBUG(Loader, "Bss size:                    0x%08X", bss_size);
    LOG_DEBUG(Loader, "Core version:                %d", core_version);
    LOG_DEBUG(Loader, "Thread priority:             0x%X", priority);
    LOG_DEBUG(Loader, "Resource limit category:     %d", resource_limit_category);
    LOG_DEBUG(Loader, "System Mode:                 %d",
              static_cast<int>(exheader_header.arm11_system_local_caps.system_mode));

    // Read ExeFS...

    exefs_offset = ncch_header.exefs_offset * kBlockSize;
    u32 exefs_size = ncch_header.exefs_size * kBlockSize;

    LOG_DEBUG(Loader, "ExeFS offset:                0x%08X", exefs_offset);
    LOG_DEBUG(Loader, "ExeFS size:                  0x%08X", exefs_size);

    file.Seek(exefs_offset + ncch_offset, SEEK_SET);
    if (file.ReadBytes(&exefs_header, sizeof(ExeFs_Header)) != sizeof(ExeFs_Header))
        return ResultStatus::Error;

    // Decrypt ExeFS
    if (exefs_aes) {
        CryptoPP::CTR_Mode<CryptoPP::AES>::Decryption dec;
        dec.SetKeyWithIV((byte*)exefs_aes->key.data(), 16, (byte*)exefs_aes->ctr.data(), 16);
        dec.ProcessData((byte*)&exefs_header, (byte*)&exefs_header, sizeof(exefs_header));
    }

    is_exefs_loaded = true;
    return ResultStatus::Success;
}

void AppLoader_NCCH::ParseRegionLockoutInfo() {
    std::vector<u8> smdh_buffer;
    if (ReadIcon(smdh_buffer) == ResultStatus::Success && smdh_buffer.size() >= sizeof(SMDH)) {
        SMDH smdh;
        memcpy(&smdh, smdh_buffer.data(), sizeof(SMDH));
        u32 region_lockout = smdh.region_lockout;
        constexpr u32 REGION_COUNT = 7;
        for (u32 region = 0; region < REGION_COUNT; ++region) {
            if (region_lockout & 1) {
                Service::CFG::SetPreferredRegionCode(region);
                break;
            }
            region_lockout >>= 1;
        }
    }
}

ResultStatus AppLoader_NCCH::Load() {
    if (is_loaded)
        return ResultStatus::ErrorAlreadyLoaded;

    ResultStatus result = LoadExeFS();
    if (result != ResultStatus::Success)
        return result;

    std::string program_id{Common::StringFromFormat("%016" PRIX64, ncch_header.program_id)};

    LOG_INFO(Loader, "Program ID: %s", program_id.c_str());

    Core::Telemetry().AddField(Telemetry::FieldType::Session, "ProgramId", program_id);

    is_loaded = true; // Set state to loaded

    result = LoadExec(); // Load the executable into memory for booting
    if (ResultStatus::Success != result)
        return result;

    Service::FS::RegisterArchiveType(std::make_unique<FileSys::ArchiveFactory_SelfNCCH>(*this),
                                     Service::FS::ArchiveIdCode::SelfNCCH);

    ParseRegionLockoutInfo();

    return ResultStatus::Success;
}

ResultStatus AppLoader_NCCH::ReadCode(std::vector<u8>& buffer) {
    return LoadSectionExeFS(".code", buffer);
}

ResultStatus AppLoader_NCCH::ReadIcon(std::vector<u8>& buffer) {
    return LoadSectionExeFS("icon", buffer);
}

ResultStatus AppLoader_NCCH::ReadBanner(std::vector<u8>& buffer) {
    return LoadSectionExeFS("banner", buffer);
}

ResultStatus AppLoader_NCCH::ReadLogo(std::vector<u8>& buffer) {
    return LoadSectionExeFS("logo", buffer);
}

ResultStatus AppLoader_NCCH::ReadProgramId(u64& out_program_id) {
    if (!file.IsOpen())
        return ResultStatus::Error;

    ResultStatus result = LoadExeFS();
    if (result != ResultStatus::Success)
        return result;

    out_program_id = ncch_header.program_id;
    return ResultStatus::Success;
}

ResultStatus AppLoader_NCCH::ReadRomFS(std::shared_ptr<FileUtil::IOFile>& romfs_file, u64& offset,
                                       u64& size) {
    if (!file.IsOpen())
        return ResultStatus::Error;

    // Check if the NCCH has a RomFS...
    if (ncch_header.romfs_offset != 0 && ncch_header.romfs_size != 0) {
        u32 romfs_offset = ncch_offset + (ncch_header.romfs_offset * kBlockSize) + 0x1000;
        u32 romfs_size = (ncch_header.romfs_size * kBlockSize) - 0x1000;

        LOG_DEBUG(Loader, "RomFS offset:           0x%08X", romfs_offset);
        LOG_DEBUG(Loader, "RomFS size:             0x%08X", romfs_size);

        if (file.GetSize() < romfs_offset + romfs_size)
            return ResultStatus::Error;

        // We reopen the file, to allow its position to be independent from file's
        romfs_file = std::make_shared<FileUtil::IOFile>(filepath, "rb");
        if (!romfs_file->IsOpen())
            return ResultStatus::Error;

        offset = romfs_offset;
        size = romfs_size;

        return ResultStatus::Success;
    }
    LOG_DEBUG(Loader, "NCCH has no RomFS");
    return ResultStatus::ErrorNotUsed;
}

} // namespace Loader
