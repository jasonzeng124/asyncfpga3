module {
  handshake.func @threshold(%arg0: !handshake.channel<i32>, %arg1: memref<1000xi32>, %arg2: memref<1000xi32>, %arg3: memref<1000xi32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["th", "red", "green", "blue", "red_start", "green_start", "blue_start", "start"], resNames = ["red_end", "green_end", "blue_end", "end"]} {
    %0:2 = lsq[%arg3 : memref<1000xi32>] (%arg6, %result, %addressResult_2, %result_8, %addressResult_14, %dataResult_15, %result_24)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1:2 = lsq[%arg2 : memref<1000xi32>] (%arg5, %result, %addressResult_0, %result_8, %addressResult_12, %dataResult_13, %result_24)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2:2 = lsq[%arg1 : memref<1000xi32>] (%arg4, %result, %addressResult, %result_8, %addressResult_10, %dataResult_11, %result_24)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq2"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %3 = constant %arg7 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %5 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %6 = br %arg7 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %7 = mux %index [%4, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %index [%5, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%6, %trueResult_22]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9 = extui %7 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = trunci %9 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%10] %2#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %11 = extui %7 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %12 = trunci %11 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_0, %dataResult_1 = load[%12] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %13 = addi %dataResult, %dataResult_1 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %14 = extui %7 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %15 = trunci %14 {handshake.bb = 1 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = load[%15] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %16 = addi %13, %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %17 = cmpi sgt, %16, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %17, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %17, %7 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %17, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %18 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %19 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_8, %index_9 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %20 = constant %result_8 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %21 = extui %19 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %22 = trunci %21 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_10, %dataResult_11 = store[%22] %20 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : <i32>, <i32>, <i32>, <i32>
    %23 = extui %19 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %24 = trunci %23 {handshake.bb = 2 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = store[%24] %20 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : <i32>, <i32>, <i32>, <i32>
    %25 = extui %19 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %26 = trunci %25 {handshake.bb = 2 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_14, %dataResult_15 = store[%26] %20 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %27 = br %18 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i32>
    %28 = br %19 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <i32>
    %29 = br %result_8 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <>
    %30 = mux %index_17 [%trueResult, %27] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %31 = mux %index_17 [%trueResult_4, %28] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_16, %index_17 = control_merge [%trueResult_6, %29]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %32 = source {handshake.bb = 3 : ui32, handshake.name = "source0"} : <>
    %33 = constant %32 {handshake.bb = 3 : ui32, handshake.name = "constant4", value = 1000 : i32} : <>, <i32>
    %34 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %35 = constant %34 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %36 = addi %31, %35 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %37 = cmpi ult, %36, %33 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %37, %36 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %37, %30 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %37, %result_16 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_24, %index_25 = control_merge [%falseResult_23]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %2#1, %1#1, %0#1, %arg7 : <>, <>, <>, <>
  }
}

