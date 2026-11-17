module {
  handshake.func @sparse(%arg0: memref<100xf32>, %arg1: memref<100xf32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "x", "a_start", "x_start", "start"], resNames = ["out0", "a_end", "x_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<100xf32>] %arg3 (%addressResult_2) %result_8 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<100xf32>] %arg2 (%addressResult) %result_8 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %0 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0.000000e+00 : f32} : <>, <f32>
    %1 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %2 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <f32>
    %3 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %4 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %5 = mux %index [%2, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %6 = mux %index [%3, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 0.000000e+00 : f32} : <>, <f32>
    %11 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %12 = trunci %11 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%12] %outputs_0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %13 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %14 = trunci %13 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = load[%14] %outputs {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <f32>, <i32>, <f32>
    %15 = mulf %dataResult, %dataResult_3 {dynamatic.predict = {location = "start", marker = 0 : i32, type = "float", values = "[0]"}, dynamatic.predict.result_idx = 0 : i32, fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf0"} : <f32>
    %16 = addf %5, %15 {dynamatic.predict = {location = "end", marker = 0 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf0"} : <f32>
    %17 = cmpf oge, %16, %10 {dynamatic.speculate = {max_predictions = 3 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %18 = addi %6, %8 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %trueResult, %falseResult = cond_br %17, %16 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <f32>
    %trueResult_4, %falseResult_5 = cond_br %17, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %17, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %19 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %19, %memEnd_1, %memEnd, %arg4 : <f32>, <>, <>, <>
  }
}

