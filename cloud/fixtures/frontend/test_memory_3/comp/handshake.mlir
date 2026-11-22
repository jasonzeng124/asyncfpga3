module {
  handshake.func @test_memory_3(%arg0: memref<4xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:2 = lsq[%arg0 : memref<4xi32>] (%arg2, %result, %addressResult, %result_10, %addressResult_12, %dataResult_13, %result_22)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg1, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %3 = mux %index [%trueResult, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_0, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_20]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %6 = trunci %5 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%6] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %7 = cmpi eq, %dataResult, %4 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %7, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %7, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %7, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %8 = merge %trueResult_4 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %9 = merge %trueResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_10, %index_11 = control_merge [%trueResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %10 = constant %result_10 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = 0 : i32} : <>, <i32>
    %11 = extui %9 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %12 = trunci %11 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = store[%12] %10 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %13 = br %8 {handshake.bb = 2 : ui32, handshake.name = "br1"} : <i32>
    %14 = br %9 {handshake.bb = 2 : ui32, handshake.name = "br2"} : <i32>
    %15 = br %result_10 {handshake.bb = 2 : ui32, handshake.name = "br3"} : <>
    %16 = mux %index_15 [%falseResult_5, %13] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_15 [%falseResult_7, %14] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%falseResult_9, %15]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %18 = source {handshake.bb = 3 : ui32, handshake.name = "source0"} : <>
    %19 = constant %18 {handshake.bb = 3 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %20 = addi %17, %19 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %21 = cmpi slt, %20, %16 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %21, %20 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %21, %16 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %21, %result_14 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %result_22, %index_23 = control_merge [%falseResult_3, %falseResult_21]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %0#1, %arg3 : <>, <>
  }
}

