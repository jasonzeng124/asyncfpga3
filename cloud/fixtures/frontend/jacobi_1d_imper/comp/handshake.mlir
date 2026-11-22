module {
  handshake.func @jacobi_1d_imper(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "A_start", "B_start", "start"], resNames = ["A_end", "B_end", "end"]} {
    %0:2 = lsq[%arg1 : memref<100xi32>] (%arg3, %result_0, %addressResult_6, %dataResult_7, %result_14, %addressResult_16, %result_32)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1:4 = lsq[%arg0 : memref<100xi32>] (%arg2, %result_0, %addressResult, %addressResult_2, %addressResult_4, %result_14, %addressResult_18, %dataResult_19, %result_32)  {groupSizes = [3 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %2 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %4 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %5 = mux %index [%3, %trueResult_28] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_30]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %7 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i32>
    %8 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %9 = br %result {handshake.bb = 1 : ui32, handshake.name = "br6"} : <>
    %10 = mux %index_1 [%7, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %11 = mux %index_1 [%8, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_0, %index_1 = control_merge [%9, %trueResult_10]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %12 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %13 = constant %12 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 99 : i32} : <>, <i32>
    %14 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %15 = constant %14 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = -1 : i32} : <>, <i32>
    %16 = constant %result_0 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %17 = addi %10, %15 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %18 = trunci %17 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i32> to <i32>
    %addressResult, %dataResult = load[%18] %1#0 {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %19 = extui %10 {handshake.bb = 2 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %20 = trunci %19 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = load[%20] %1#1 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %21 = addi %dataResult, %dataResult_3 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %22 = addi %10, %16 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %23 = extui %22 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %24 = trunci %23 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_4, %dataResult_5 = load[%24] %1#2 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %25 = addi %21, %dataResult_5 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %26 = shli %25, %16 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i32>
    %27 = addi %25, %26 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i32>
    %28 = extui %10 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %29 = trunci %28 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_6, %dataResult_7 = store[%29] %27 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : <i32>, <i32>, <i32>, <i32>
    %30 = addi %10, %16 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i32>
    %31 = cmpi ult, %30, %13 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %31, %30 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %31, %11 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %31, %result_0 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %trueResult_12, %falseResult_13 = cond_br %31, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %32 = mux %index_15 [%falseResult_13, %trueResult_20] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %33 = mux %index_15 [%falseResult_9, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%falseResult_11, %trueResult_24]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %34 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %35 = constant %34 {handshake.bb = 3 : ui32, handshake.name = "constant9", value = 99 : i32} : <>, <i32>
    %36 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %37 = constant %36 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %38 = extui %32 {handshake.bb = 3 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %39 = trunci %38 {handshake.bb = 3 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_16, %dataResult_17 = load[%39] %0#0 {handshake.bb = 3 : ui32, handshake.name = "load4"} : <i32>, <i32>, <i32>, <i32>
    %40 = extui %32 {handshake.bb = 3 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %41 = trunci %40 {handshake.bb = 3 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_18, %dataResult_19 = store[%41] %dataResult_17 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %42 = addi %32, %37 {handshake.bb = 3 : ui32, handshake.name = "addi5"} : <i32>
    %43 = cmpi ult, %42, %35 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %43, %42 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %43, %33 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %43, %result_14 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %44 = merge %falseResult_23 {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i32>
    %result_26, %index_27 = control_merge [%falseResult_25]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    %45 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %46 = constant %45 {handshake.bb = 4 : ui32, handshake.name = "constant11", value = 3 : i32} : <>, <i32>
    %47 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %48 = constant %47 {handshake.bb = 4 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %49 = addi %44, %48 {handshake.bb = 4 : ui32, handshake.name = "addi6"} : <i32>
    %50 = cmpi ult, %49, %46 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_28, %falseResult_29 = cond_br %50, %49 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %50, %result_26 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %result_32, %index_33 = control_merge [%falseResult_31]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %1#3, %0#1, %arg4 : <>, <>, <>
  }
}

