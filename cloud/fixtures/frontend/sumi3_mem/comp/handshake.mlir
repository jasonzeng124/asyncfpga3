module {
  handshake.func @sumi3_mem(%arg0: memref<1000xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<1000xi32>] %arg1 (%addressResult) %result_4 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %2 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %3 = mux %index [%1, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%1, %trueResult_0] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_2]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1000 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %9 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = trunci %9 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%10] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %11 = muli %dataResult, %dataResult {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %12 = muli %11, %dataResult {handshake.bb = 1 : ui32, handshake.name = "muli1"} : <i32>
    %13 = addi %4, %12 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %14 = addi %3, %8 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %15 = cmpi ult, %14, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %15, %14 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %15, %13 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %15, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %16 = merge %falseResult_1 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_4, %index_5 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %16, %memEnd, %arg2 : <i32>, <>, <>
  }
}

