module {
  handshake.func @test_memory_17(%arg0: memref<4xi32>, %arg1: memref<4xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %0:2 = lsq[%arg1 : memref<4xi32>] (%arg3, %result, %addressResult, %result_4, %addressResult_6, %dataResult_7, %result_16)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %memEnd = mem_controller[%arg0 : memref<4xi32>] %arg2 (%18, %addressResult_10, %dataResult_11) %result_16 {connectedBlocks = [3 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %1 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %3 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = mux %index [%2, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 5 : i32} : <>, <i32>
    %8 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %9 = trunci %8 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%9] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %10 = cmpi sgt, %dataResult, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %10, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %10, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %10, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %11 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_4, %index_5 = control_merge [%trueResult_0]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %12 = constant %result_4 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %13 = extui %11 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %14 = trunci %13 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_6, %dataResult_7 = store[%14] %12 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %15 = br %12 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i32>
    %16 = br %11 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i32>
    %17 = br %result_4 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <>
    %18 = constant %result_8 {handshake.bb = 3 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %19 = mux %index_9 [%falseResult_3, %15] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %20 = mux %index_9 [%falseResult, %16] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_8, %index_9 = control_merge [%falseResult_1, %17]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %21 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %22 = constant %21 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = 4 : i32} : <>, <i32>
    %23 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %24 = constant %23 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %25 = extui %20 {handshake.bb = 3 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %26 = trunci %25 {handshake.bb = 3 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_10, %dataResult_11 = store[%26] %19 {handshake.bb = 3 : ui32, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %27 = addi %20, %24 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %28 = cmpi ult, %27, %22 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %28, %27 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %28, %result_8 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %result_16, %index_17 = control_merge [%falseResult_15]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd, %0#1, %arg4 : <>, <>, <>
  }
}

