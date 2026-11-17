module {
  handshake.func @sparse(%arg0: memref<100xf32>, %arg1: memref<100xf32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "x", "a_start", "x_start", "start"], resNames = ["out0", "a_end", "x_end", "end"]} {
    %0:4 = fork [4] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg1 : memref<100xf32>] %arg3 (%addressResult_2) %24#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i7>) -> !handshake.channel<f32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<100xf32>] %arg2 (%addressResult) %24#0 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i7>) -> !handshake.channel<f32>
    %1 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0.000000e+00 : f32} : <>, <f32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <f32>
    %3 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %5 = extui %4 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %7 = mux %12#0 [%2, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %8 = mux %12#1 [%5, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %9:3 = fork [3] %8 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %10 = trunci %9#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i7>
    %11 = trunci %9#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i7>
    %result, %index = control_merge [%6, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 0.000000e+00 : f32} : <>, <f32>
    %addressResult, %dataResult = load[%11] %outputs_0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i7>, <f32>, <i7>, <f32>
    %addressResult_2, %dataResult_3 = load[%10] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i7>, <f32>, <i7>, <f32>
    %17 = mulf %dataResult, %dataResult_3 {dynamatic.predict = {location = "start", marker = 0 : i32, type = "float", values = "[0]"}, dynamatic.predict.result_idx = 0 : i32, fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf0"} : <f32>
    %18 = addf %7, %17 {dynamatic.predict = {location = "end", marker = 0 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf0"} : <f32>
    %19:2 = fork [2] %18 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <f32>
    %20 = cmpf oge, %19#1, %16 {dynamatic.speculate = {max_predictions = 3 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %21:3 = fork [3] %20 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %22 = addi %9#2, %14 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %trueResult, %falseResult = cond_br %21#2, %19#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <f32>
    %trueResult_4, %falseResult_5 = cond_br %21#1, %22 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink0"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %21#0, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %23 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_9 {handshake.name = "sink1"} : <i1>
    %24:2 = fork [2] %result_8 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %23, %memEnd_1, %memEnd, %0#1 : <f32>, <>, <>, <>
  }
}

