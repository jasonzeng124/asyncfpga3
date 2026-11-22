module {
  handshake.func @nested_conditionals_1(%arg0: memref<100xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "c", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:2 = lsq[%arg0 : memref<100xi32>] (%arg2, %result, %addressResult, %result_12, %addressResult_14, %dataResult_15, %result_22)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %3 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %4 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <>
    %5 = mux %index [%2, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%3, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_20]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 8 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 2 : i32} : <>, <i32>
    %11 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %12 = trunci %11 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%12] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %13 = addi %dataResult, %10 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %14 = cmpi sgt, %dataResult, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %14, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %14, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %14, %13 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %14, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %trueResult_6, %falseResult_7 = cond_br %14, %dataResult {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %15 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %16 = merge %trueResult_0 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %17 = merge %trueResult_2 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %result_8, %index_9 = control_merge [%trueResult_4]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %18 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %19 = constant %18 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 5 : i32} : <>, <i32>
    %22 = cmpi sgt, %15, %21 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %23 = shli %17, %19 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i32>
    %24 = addi %17, %15 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %25 = select %22[%23, %24] {handshake.bb = 2 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %26 = br %25 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <i32>
    %27 = br %15 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <i32>
    %28 = br %16 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <i32>
    %29 = br %result_8 {handshake.bb = 2 : ui32, handshake.name = "br9"} : <>
    %30 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <i32>
    %31 = merge %falseResult_1 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i32>
    %32 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %33 = merge %falseResult_3 {handshake.bb = 3 : ui32, handshake.name = "merge6"} : <i32>
    %result_10, %index_11 = control_merge [%falseResult_5]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %34 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %35 = constant %34 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = -1 : i32} : <>, <i32>
    %36 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %37 = constant %36 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 0 : i32} : <>, <i32>
    %38 = cmpi eq, %30, %37 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %39 = addi %32, %35 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %40 = muli %33, %30 {handshake.bb = 3 : ui32, handshake.name = "muli0"} : <i32>
    %41 = select %38[%39, %40] {handshake.bb = 3 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %42 = br %41 {handshake.bb = 3 : ui32, handshake.name = "br10"} : <i32>
    %43 = br %30 {handshake.bb = 3 : ui32, handshake.name = "br11"} : <i32>
    %44 = br %31 {handshake.bb = 3 : ui32, handshake.name = "br12"} : <i32>
    %45 = br %result_10 {handshake.bb = 3 : ui32, handshake.name = "br13"} : <>
    %46 = mux %index_13 [%26, %42] {handshake.bb = 4 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %47 = mux %index_13 [%27, %43] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %48 = mux %index_13 [%28, %44] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_12, %index_13 = control_merge [%29, %45]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %49 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %50 = constant %49 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 100 : i32} : <>, <i32>
    %51 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %52 = constant %51 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 3 : i32} : <>, <i32>
    %53 = source {handshake.bb = 4 : ui32, handshake.name = "source8"} : <>
    %54 = constant %53 {handshake.bb = 4 : ui32, handshake.name = "constant16", value = 1 : i32} : <>, <i32>
    %55 = addi %46, %52 {dynamatic.predict = {location = "end", marker = 0 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i32>
    %56 = extui %48 {handshake.bb = 4 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %57 = trunci %56 {handshake.bb = 4 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_14, %dataResult_15 = store[%57] %55 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %58 = addi %48, %54 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i32>
    %59 = cmpi ult, %58, %50 {handshake.bb = 4 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %59, %58 {handshake.bb = 4 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %59, %47 {handshake.bb = 4 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %59, %result_12 {handshake.bb = 4 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %result_22, %index_23 = control_merge [%falseResult_21]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %0#1, %arg3 : <>, <>
  }
}

