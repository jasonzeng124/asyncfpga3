module {
  handshake.func @test_memory_13(%arg0: memref<4xi32>, %arg1: memref<4xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %0:2 = lsq[%arg1 : memref<4xi32>] (%arg3, %result, %addressResult_0, %result_6, %addressResult_8, %dataResult_9, %result_18)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1:2 = lsq[%arg0 : memref<4xi32>] (%arg2, %result, %addressResult, %result_10, %addressResult_12, %dataResult_13, %result_18)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %4 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %5 = mux %index [%3, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_16]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 5 : i32} : <>, <i32>
    %8 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %9 = trunci %8 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%9] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %10 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %11 = trunci %10 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_0, %dataResult_1 = load[%11] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %12 = cmpi sgt, %dataResult_1, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %12, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %12, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_4, %falseResult_5 = cond_br %12, %dataResult {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %13 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_6, %index_7 = control_merge [%trueResult_2]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %14 = constant %result_6 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 0 : i32} : <>, <i32>
    %15 = extui %13 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %16 = trunci %15 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_8, %dataResult_9 = store[%16] %14 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %17 = br %14 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i32>
    %18 = br %13 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i32>
    %19 = br %result_6 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <>
    %20 = mux %index_11 [%falseResult_5, %17] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %21 = mux %index_11 [%falseResult, %18] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%falseResult_3, %19]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %22 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %23 = constant %22 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 4 : i32} : <>, <i32>
    %24 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %25 = constant %24 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %26 = extui %21 {handshake.bb = 3 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %27 = trunci %26 {handshake.bb = 3 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = store[%27] %20 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : <i32>, <i32>, <i32>, <i32>
    %28 = addi %21, %25 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %29 = cmpi ult, %28, %23 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %29, %28 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %29, %result_10 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %result_18, %index_19 = control_merge [%falseResult_17]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %1#1, %0#1, %arg4 : <>, <>, <>
  }
}

