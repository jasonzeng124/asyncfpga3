module {
  handshake.func @nested_conditionals_2(%arg0: memref<100xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "c", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:2 = lsq[%arg0 : memref<100xi32>] (%arg2, %result, %addressResult, %result_14, %addressResult_16, %dataResult_17, %result_26)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %2 = constant %1 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %3 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %4 = constant %3 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = 3 : i32} : <>, <i32>
    %5 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %6 = shli %arg1, %2 {handshake.bb = 0 : ui32, handshake.name = "shli2"} : <i32>
    %7 = shli %arg1, %4 {handshake.bb = 0 : ui32, handshake.name = "shli3"} : <i32>
    %8 = addi %6, %7 {handshake.bb = 0 : ui32, handshake.name = "addi4"} : <i32>
    %9 = br %5 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %10 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %11 = br %8 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <i32>
    %12 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %13 = mux %index [%9, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %14 = mux %index [%10, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %15 = mux %index [%11, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%12, %trueResult_24]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %17 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %18 = extui %13 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %19 = trunci %18 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%19] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %20 = shli %dataResult, %17 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %21 = cmpi sgt, %dataResult, %17 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %21, %14 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %21, %15 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %21, %13 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %21, %dataResult {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %21, %20 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %21, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %22 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %23 = merge %trueResult_0 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %24 = merge %trueResult_2 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %25 = merge %trueResult_4 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %26 = merge %trueResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge4"} : <i32>
    %result_10, %index_11 = control_merge [%trueResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %28 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 2 : i32} : <>, <i32>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %30 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 5 : i32} : <>, <i32>
    %31 = cmpi sgt, %22, %30 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %32 = shli %25, %28 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i32>
    %33 = addi %26, %22 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %34 = select %31[%32, %33] {handshake.bb = 2 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %35 = br %34 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <i32>
    %36 = br %22 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <i32>
    %37 = br %23 {handshake.bb = 2 : ui32, handshake.name = "br9"} : <i32>
    %38 = br %24 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <i32>
    %39 = br %result_10 {handshake.bb = 2 : ui32, handshake.name = "br11"} : <>
    %40 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <i32>
    %41 = merge %falseResult_1 {handshake.bb = 3 : ui32, handshake.name = "merge6"} : <i32>
    %42 = merge %falseResult_3 {handshake.bb = 3 : ui32, handshake.name = "merge7"} : <i32>
    %43 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge8"} : <i32>
    %result_12, %index_13 = control_merge [%falseResult_9]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %44 = addi %41, %43 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i32>
    %45 = br %44 {handshake.bb = 3 : ui32, handshake.name = "br12"} : <i32>
    %46 = br %40 {handshake.bb = 3 : ui32, handshake.name = "br13"} : <i32>
    %47 = br %41 {handshake.bb = 3 : ui32, handshake.name = "br14"} : <i32>
    %48 = br %42 {handshake.bb = 3 : ui32, handshake.name = "br15"} : <i32>
    %49 = br %result_12 {handshake.bb = 3 : ui32, handshake.name = "br16"} : <>
    %50 = mux %index_15 [%35, %45] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %51 = mux %index_15 [%36, %46] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %52 = mux %index_15 [%37, %47] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %53 = mux %index_15 [%38, %48] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%39, %49]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %54 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %55 = constant %54 {handshake.bb = 4 : ui32, handshake.name = "constant10", value = 100 : i32} : <>, <i32>
    %56 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %57 = constant %56 {handshake.bb = 4 : ui32, handshake.name = "constant11", value = 3 : i32} : <>, <i32>
    %58 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %59 = constant %58 {handshake.bb = 4 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %60 = addi %50, %57 {dynamatic.predict = {location = "end", marker = 0 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 4 : ui32, handshake.name = "addi2"} : <i32>
    %61 = extui %53 {handshake.bb = 4 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %62 = trunci %61 {handshake.bb = 4 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_16, %dataResult_17 = store[%62] %60 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %63 = addi %53, %59 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i32>
    %64 = cmpi ult, %63, %55 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %64, %63 {handshake.bb = 4 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %64, %51 {handshake.bb = 4 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %64, %52 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %64, %result_14 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %result_26, %index_27 = control_merge [%falseResult_25]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %0#1, %arg3 : <>, <>
  }
}

