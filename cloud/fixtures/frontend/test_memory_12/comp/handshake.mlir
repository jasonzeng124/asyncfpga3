module {
  handshake.func @test_memory_12(%arg0: memref<4xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["a_end", "end"]} {
    %memEnd = mem_controller[%arg0 : memref<4xi32>] %arg1 (%0, %addressResult, %dataResult, %addressResult_0, %dataResult_1, %addressResult_2, %dataResult_3, %16, %addressResult_8, %dataResult_9) %result_16 {connectedBlocks = [0 : i32, 2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 3 : i32} : <>, <i32>
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = 2 : i32} : <>, <i32>
    %2 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %3 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %5 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = 2 : i32} : <>, <i32>
    %6 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = store[%6] %3 {handshake.bb = 0 : ui32, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_0, %dataResult_1 = store[%2] %4 {handshake.bb = 0 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %addressResult_2, %dataResult_3 = store[%1] %5 {handshake.bb = 0 : ui32, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %7 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %8 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %9 = mux %index [%7, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%8, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 0 : i32} : <>, <i32>
    %14 = andi %9, %11 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i32>
    %15 = cmpi eq, %14, %13 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %15, %9 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %15, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %16 = constant %result_6 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %17 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_6, %index_7 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %18 = constant %result_6 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 3 : i32} : <>, <i32>
    %19 = constant %result_6 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 3 : i32} : <>, <i32>
    %addressResult_8, %dataResult_9 = store[%19] %18 {handshake.bb = 2 : ui32, handshake.name = "store3"} : <i32>, <i32>, <i32>, <i32>
    %20 = br %17 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i32>
    %21 = br %result_6 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <>
    %22 = mux %index_11 [%trueResult, %20] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%trueResult_4, %21]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %23 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %24 = constant %23 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 4 : i32} : <>, <i32>
    %25 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %26 = constant %25 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 1 : i32} : <>, <i32>
    %27 = addi %22, %26 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %28 = cmpi ult, %27, %24 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %28, %27 {handshake.bb = 3 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %28, %result_10 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %result_16, %index_17 = control_merge [%falseResult_15]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd, %arg2 : <>, <>
  }
}

