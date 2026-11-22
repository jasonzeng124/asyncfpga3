module {
  handshake.func @if_convert(%arg0: memref<200xi32>, %arg1: memref<200xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %memEnd = mem_controller[%arg1 : memref<200xi32>] %arg3 (%3, %addressResult_1, %dataResult_2) %result_5 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg0 : memref<200xi32>] %arg2 (%addressResult) %result_5 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %2 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %3 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %4 = mux %index [%1, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_3]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 198 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 10000 : i32} : <>, <i32>
    %9 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %10 = trunci %4 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i32> to <i32>
    %addressResult, %dataResult = load[%10] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %11 = muli %4, %dataResult {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %12 = cmpi slt, %11, %8 {dynamatic.speculate = {max_predictions = 8 : i64, style = "standard"}, dynamatic.speculate.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %13 = addi %4, %9 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %14 = select %12[%13, %4] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %15 = addi %14, %9 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %16 = trunci %15 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_1, %dataResult_2 = store[%16] %9 {handshake.bb = 1 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %17 = cmpi slt, %14, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult, %falseResult = cond_br %17, %15 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_3, %falseResult_4 = cond_br %17, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_5, %index_6 = control_merge [%falseResult_4]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd_0, %memEnd, %arg4 : <>, <>, <>
  }
}

