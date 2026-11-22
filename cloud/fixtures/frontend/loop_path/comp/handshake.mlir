module {
  handshake.func @loop_path(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: memref<1000xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "a_start", "b_start", "c_start", "start"], resNames = ["a_end", "b_end", "c_end", "end"]} {
    %memEnd = mem_controller[%arg2 : memref<1000xi32>] %arg5 (%3, %addressResult_5, %dataResult_6) %result_9 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<1000xi32>] %arg4 (%addressResult_3) %result_9 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<1000xi32>] %arg3 (%addressResult) %result_9 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %2 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %3 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %4 = mux %index [%1, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_7]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 999 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 1000 : i32} : <>, <i32>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 2 : i32} : <>, <i32>
    %13 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %14 = trunci %13 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%14] %outputs_1 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %15 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %16 = trunci %15 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_3, %dataResult_4 = load[%16] %outputs {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %17 = addi %dataResult, %dataResult_4 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %18 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %19 = trunci %18 {handshake.bb = 1 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_5, %dataResult_6 = store[%19] %17 {handshake.bb = 1 : ui32, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %20 = subi %10, %17 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %21 = shli %17, %12 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %22 = addi %17, %21 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %23 = cmpi sgt, %20, %22 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %24 = cmpi ult, %4, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %25 = andi %23, %24 {dynamatic.speculate = {max_predictions = 4 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %26 = addi %4, %6 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %trueResult, %falseResult = cond_br %25, %26 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_7, %falseResult_8 = cond_br %25, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_9, %index_10 = control_merge [%falseResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd_2, %memEnd_0, %memEnd, %arg6 : <>, <>, <>, <>
  }
}

