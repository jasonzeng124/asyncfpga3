module {
  handshake.func @test_memory_8(%arg0: memref<4xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:4 = lsq[%arg0 : memref<4xi32>] (%arg2, %result, %addressResult, %addressResult_4, %result_12, %addressResult_14, %addressResult_16, %dataResult_17, %addressResult_18, %dataResult_19, %result_28)  {groupSizes = [2 : i32, 3 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 2 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg1, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %3 = mux %index [%trueResult, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_0, %trueResult_24] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_26]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = -5 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = -2 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = -1 : i32} : <>, <i32>
    %11 = addi %3, %10 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %12 = trunci %11 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i32> to <i32>
    %addressResult, %dataResult = load[%12] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %13 = addi %3, %8 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %14 = trunci %13 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_4, %dataResult_5 = load[%14] %0#1 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %15 = addi %dataResult, %dataResult_5 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %16 = cmpi sgt, %15, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %16, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %16, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %16, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %17 = merge %trueResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %18 = merge %trueResult_8 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_12, %index_13 = control_merge [%trueResult_10]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %19 = constant %result_12 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = -1 : i32} : <>, <i32>
    %22 = extui %18 {handshake.bb = 2 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %23 = trunci %22 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_14, %dataResult_15 = load[%23] %0#2 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %24 = addi %18, %21 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %25 = trunci %24 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i32> to <i32>
    %addressResult_16, %dataResult_17 = store[%25] %dataResult_15 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : <i32>, <i32>, <i32>, <i32>
    %26 = extui %18 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %27 = trunci %26 {handshake.bb = 2 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_18, %dataResult_19 = store[%27] %19 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : <i32>, <i32>, <i32>, <i32>
    %28 = br %17 {handshake.bb = 2 : ui32, handshake.name = "br1"} : <i32>
    %29 = br %18 {handshake.bb = 2 : ui32, handshake.name = "br2"} : <i32>
    %30 = br %result_12 {handshake.bb = 2 : ui32, handshake.name = "br3"} : <>
    %31 = mux %index_21 [%falseResult_7, %28] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %32 = mux %index_21 [%falseResult_9, %29] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_20, %index_21 = control_merge [%falseResult_11, %30]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %33 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %34 = constant %33 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 1 : i32} : <>, <i32>
    %35 = addi %32, %34 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i32>
    %36 = cmpi slt, %35, %31 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_22, %falseResult_23 = cond_br %36, %35 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %36, %31 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %36, %result_20 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %result_28, %index_29 = control_merge [%falseResult_3, %falseResult_27]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %0#3, %arg3 : <>, <>
  }
}

