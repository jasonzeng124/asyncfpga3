module {
  handshake.func @if_loop_add(%arg0: memref<1000xf32>, %arg1: memref<1000xf32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["out0", "a_end", "b_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xf32>] %arg3 (%addressResult_2) %result_8 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<1000xf32>] %arg2 (%addressResult) %result_8 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %0 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0.000000e+00 : f32} : <>, <f32>
    %1 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %2 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <f32>
    %3 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %4 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %5 = mux %index [%2, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %6 = mux %index [%3, %trueResult_4] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_6]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1000 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 0.000000e+00 : f32} : <>, <f32>
    %13 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %14 = trunci %13 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%14] %outputs_0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %15 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %16 = trunci %15 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = load[%16] %outputs {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <f32>, <i32>, <f32>
    %17 = subf %dataResult, %dataResult_3 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "subf0"} : <f32>
    %18 = cmpf ult, %17, %12 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %19 = addf %5, %17 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf0"} : <f32>
    %20 = select %18[%5, %19] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <f32>
    %21 = addi %6, %10 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %22 = cmpi ult, %21, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %22, %20 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <f32>
    %trueResult_4, %falseResult_5 = cond_br %22, %21 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %22, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %23 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %23, %memEnd_1, %memEnd, %arg4 : <f32>, <>, <>, <>
  }
}

