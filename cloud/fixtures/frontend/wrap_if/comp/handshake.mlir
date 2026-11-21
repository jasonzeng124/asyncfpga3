module {
  handshake.func @wrap_if(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "c", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %memEnd = mem_controller[%arg1 : memref<100xi32>] %arg4 (%16, %addressResult_8, %dataResult_9) %result_20 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %0:2 = lsq[%arg0 : memref<100xi32>] (%arg3, %result, %addressResult, %result_10, %addressResult_12, %dataResult_13, %result_20)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %3 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %4 = br %arg5 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %5 = mux %index [%2, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%3, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_18]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %11 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %12 = trunci %11 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%12] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %13 = shli %dataResult, %8 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %14 = addi %dataResult, %13 {dynamatic.predict = {location = "start", marker = 0 : i32, type = "int", values = "[3,-4,5]"}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %15 = cmpi sgt, %dataResult, %10 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %15, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %15, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %15, %14 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %15, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %16 = constant %result_6 {handshake.bb = 2 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %17 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %18 = merge %trueResult_0 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %19 = merge %trueResult_2 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %result_6, %index_7 = control_merge [%trueResult_4]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 1 : i32} : <>, <i32>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %23 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 3 : i32} : <>, <i32>
    %24 = addi %19, %17 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %25 = shli %24, %21 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i32>
    %26 = shli %24, %23 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i32>
    %27 = addi %25, %26 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %28 = extui %18 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %29 = trunci %28 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_8, %dataResult_9 = store[%29] %27 {handshake.bb = 2 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %30 = br %19 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i32>
    %31 = br %17 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <i32>
    %32 = br %18 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <i32>
    %33 = br %result_6 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <>
    %34 = mux %index_11 [%falseResult_3, %30] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %35 = mux %index_11 [%falseResult, %31] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %36 = mux %index_11 [%falseResult_1, %32] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_10, %index_11 = control_merge [%falseResult_5, %33]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %37 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %38 = constant %37 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 100 : i32} : <>, <i32>
    %39 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %40 = constant %39 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %41 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %42 = constant %41 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 3 : i32} : <>, <i32>
    %43 = subi %34, %35 {handshake.bb = 3 : ui32, handshake.name = "subi0"} : <i32>
    %44 = shli %43, %40 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i32>
    %45 = shli %43, %42 {handshake.bb = 3 : ui32, handshake.name = "shli4"} : <i32>
    %46 = addi %44, %45 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i32>
    %47 = addi %43, %46 {handshake.bb = 3 : ui32, handshake.name = "addi5"} : <i32>
    %48 = extui %36 {handshake.bb = 3 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %49 = trunci %48 {handshake.bb = 3 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = store[%49] %47 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %50 = addi %36, %40 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i32>
    %51 = cmpi ult, %50, %38 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %51, %50 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %51, %35 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %51, %result_10 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_20, %index_21 = control_merge [%falseResult_19]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %0#1, %memEnd, %arg5 : <>, <>, <>
  }
}

