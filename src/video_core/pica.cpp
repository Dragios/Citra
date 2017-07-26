// Copyright 2015 Citra Emulator Project
// Licensed under GPLv2 or any later version
// Refer to the license.txt file included.

#include <cstring>
#include "video_core/pica.h"
#include "video_core/pica_state.h"
#include "video_core/regs_pipeline.h"

namespace Pica {

State g_state;

void Init() {
    g_state.Reset();
}

void Shutdown() {
    Shader::Shutdown();
}

template <typename T>
void Zero(T& o) {
    memset(&o, 0, sizeof(o));
}

void State::Reset() {
    Zero(regs);
    Zero(vs);
    Zero(gs);
    Zero(cmd_list);
    Zero(immediate);
    shader_pipe.Reset(this);
    primitive_assembler.Reconfigure(PipelineRegs::TriangleTopology::List);
}

void ShaderPipe::Reset(State* state) {
    gs_input_buffer_begin = gs_input_buffer_end = gs_input_buffer_cur = nullptr;
    mode = static_cast<PipelineRegs::GSMode>(0xFFFFFFFF);
    this->state = state;
}

void ShaderPipe::Setup(Shader::ShaderEngine* shader_engine, Shader::GSUnitState* gs_unit,
                       Shader::GSEmitter::VertexHandler vertex_handler,
                       Shader::GSEmitter::WindingSetter winding_setter) {
    this->shader_engine = shader_engine;
    this->gs_unit = gs_unit;

    shader_engine->SetupBatch(state->gs, state->regs.gs.main_offset);
    gs_unit->SetupEmitter(state->regs.gs, vertex_handler, winding_setter);
}

void ShaderPipe::Reconfigure() {
    ASSERT_MSG(gs_input_buffer_cur == gs_input_buffer_begin,
               "Reconfigure while buffer is not empty!");

    ASSERT(state->regs.pipeline.vs_outmap_total_minus_1_a ==
           state->regs.pipeline.vs_outmap_total_minus_1_b);
    num_vs_to_gs = state->regs.pipeline.vs_outmap_total_minus_1_a + 1;

    switch (mode = state->regs.pipeline.gs_config.mode) {
    case PipelineRegs::GSMode::Point:
        gs_input_buffer_cur = gs_input_buffer_begin = gs_input_point_mode.attr;
        gs_input_buffer_end =
            gs_input_buffer_begin + (state->regs.gs.max_input_attribute_index + 1);
        need_vertex_num = false;
        break;
    default:
        ASSERT(false);
    }
}

bool ShaderPipe::NeedAttributeNum() {
    return need_vertex_num;
}

void ShaderPipe::PutAttributeNum(size_t num) {
    ASSERT(need_vertex_num);
    // TODO
    need_vertex_num = false;
}

void ShaderPipe::PutAttribute(const Math::Vec4<float24>* input) {
    ASSERT(gs_input_buffer_cur + num_vs_to_gs <= gs_input_buffer_end);
    gs_input_buffer_cur = std::copy(input, input + num_vs_to_gs, gs_input_buffer_cur);
    if (gs_input_buffer_cur == gs_input_buffer_end) {
        gs_unit->LoadInput(state->regs.gs, gs_input_point_mode);
        shader_engine->Run(state->gs, *gs_unit);
        gs_input_buffer_cur = gs_input_buffer_begin;
    }
}
}
