module {
  handshake.func @test_memory_6(%arg0: memref<4xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:3 = lsq[%arg0 : memref<4xi32>] (%arg2, %result, %addressResult, %addressResult_4, %addressResult_6, %dataResult_7, %addressResult_8, %dataResult_9, %result_16)  {groupSizes = [4 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 2 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg1, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %3 = mux %index [%trueResult, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_0, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %7 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %8 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %9 = constant %8 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 5 : i32} : <>, <i32>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = -2 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = -1 : i32} : <>, <i32>
    %14 = addi %3, %13 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %15 = trunci %14 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i32> to <i32>
    %addressResult, %dataResult = load[%15] %0#0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %16 = addi %3, %11 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %17 = trunci %16 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_4, %dataResult_5 = load[%17] %0#1 {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %18 = addi %dataResult, %dataResult_5 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %19 = addi %18, %9 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %20 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %21 = trunci %20 {handshake.bb = 1 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_6, %dataResult_7 = store[%21] %19 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %22 = addi %3, %13 {handshake.bb = 1 : ui32, handshake.name = "addi4"} : <i32>
    %23 = trunci %22 {handshake.bb = 1 : ui32, handshake.name = "index_cast3"} : <i32> to <i32>
    %addressResult_8, %dataResult_9 = store[%23] %7 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : <i32>, <i32>, <i32>, <i32>
    %24 = addi %3, %6 {handshake.bb = 1 : ui32, handshake.name = "addi5"} : <i32>
    %25 = cmpi slt, %24, %4 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %25, %24 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %25, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %25, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_16, %index_17 = control_merge [%falseResult_3, %falseResult_15]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %0#2, %arg3 : <>, <>
  }
}

