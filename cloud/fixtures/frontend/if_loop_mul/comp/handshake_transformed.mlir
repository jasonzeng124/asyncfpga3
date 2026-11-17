module {
  handshake.func @if_loop_mul(%arg0: memref<1000xf32>, %arg1: memref<1000xf32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["out0", "a_end", "b_end", "end"]} {
    %0:4 = fork [4] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xf32>] %arg3 (%addressResult_2) %30#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<1000xf32>] %arg2 (%addressResult) %30#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %1 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1.000000e+00 : f32} : <>, <f32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <f32>
    %3 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %5 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i1> to <i10>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %7 = mux %13#1 [%2, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <f32>
    %9 = mux %13#0 [%5, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i10>, <i10>] to <i10>
    %10:3 = fork [3] %9 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i10>
    %11 = extui %10#2 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i10> to <i11>
    %12 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i11} : <>, <i11>
    %result, %index = control_merge [%6, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %13:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %17 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0.000000e+00 : f32} : <>, <f32>
    %addressResult, %dataResult = load[%10#1] %outputs_0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <f32>, <i10>, <f32>
    %addressResult_2, %dataResult_3 = load[%10#0] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <f32>, <i10>, <f32>
    %18 = subf %dataResult, %dataResult_3 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "subf0"} : <f32>
    %19:2 = fork [2] %18 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <f32>
    %20 = cmpf ult, %19#1, %17 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %21 = mulf %8#1, %19#0 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf0"} : <f32>
    %22 = select %20[%8#0, %21] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <f32>
    %23 = addi %11, %12 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i11>
    %24:2 = fork [2] %23 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i11>
    %25 = trunci %24#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i11> to <i10>
    %26 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1000 : i11} : <>, <i11>
    %27 = cmpi ult, %24#1, %26 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i11>
    %28:3 = fork [3] %27 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult, %falseResult = cond_br %28#1, %22 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <f32>
    %trueResult_4, %falseResult_5 = cond_br %28#0, %25 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i10>
    sink %falseResult_5 {handshake.name = "sink0"} : <i10>
    %trueResult_6, %falseResult_7 = cond_br %28#2, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %29 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_9 {handshake.name = "sink1"} : <i1>
    %30:2 = fork [2] %result_8 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %29, %memEnd_1, %memEnd, %0#1 : <f32>, <>, <>, <>
  }
}

