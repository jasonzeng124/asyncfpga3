module {
  handshake.func @test_memory_4(%arg0: memref<4xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:2 = lsq[%arg0 : memref<4xi32>] (%arg2, %result, %addressResult, %dataResult, %addressResult_4, %result_14)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %2 = constant %1 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = -1 : i32} : <>, <i32>
    %3 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %4 = addi %arg1, %2 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    %5 = cmpi sgt, %4, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %5, %3 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %5, %4 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %5, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %6 = mux %index [%trueResult, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %index [%trueResult, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %index [%trueResult_0, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_12]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %11 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %12 = trunci %11 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = store[%12] %7 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %13 = addi %6, %10 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %14 = extui %13 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %15 = trunci %14 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_4, %dataResult_5 = load[%15] %0#0 {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %16 = addi %6, %10 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %17 = cmpi slt, %16, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %17, %16 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %17, %dataResult_5 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %17, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %17, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_14, %index_15 = control_merge [%falseResult_3, %falseResult_13]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %0#1, %arg3 : <>, <>
  }
}

