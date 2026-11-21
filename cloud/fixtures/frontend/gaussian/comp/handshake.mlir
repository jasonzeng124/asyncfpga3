module {
  handshake.func @gaussian(%arg0: memref<20xi32>, %arg1: memref<400xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["c", "a", "c_start", "a_start", "start"], resNames = ["out0", "c_end", "a_end", "end"]} {
    %0:3 = lsq[%arg1 : memref<400xi32>] (%arg3, %result_14, %addressResult, %addressResult_18, %addressResult_20, %dataResult_21, %result_44)  {groupSizes = [3 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %outputs, %memEnd = mem_controller[%arg0 : memref<20xi32>] %arg2 (%addressResult_16) %result_44 {connectedBlocks = [4 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %3 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = mux %index [%2, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_42]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 19 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %9 = addi %4, %8 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %10 = cmpi ult, %9, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %10, %9 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %10, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %10, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %11 = merge %falseResult_25 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %12 = merge %falseResult_27 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_4, %index_5 = control_merge [%falseResult_37]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %13 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %14 = constant %13 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 19 : i32} : <>, <i32>
    %15 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %16 = constant %15 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %17 = addi %12, %16 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %18 = cmpi ult, %17, %14 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %18, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %18, %11 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %18, %result_4 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %19 = mux %index_13 [%trueResult, %trueResult_6] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %20 = mux %index_13 [%trueResult_0, %trueResult_8] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_12, %index_13 = control_merge [%trueResult_2, %trueResult_10]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %21 = constant %result_12 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 1 : i32} : <>, <i32>
    %22 = extui %19 {handshake.bb = 3 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %23 = extui %20 {handshake.bb = 3 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %24 = extui %20 {handshake.bb = 3 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %25 = extui %19 {handshake.bb = 3 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %26 = br %21 {handshake.bb = 3 : ui32, handshake.name = "br4"} : <i32>
    %27 = br %20 {handshake.bb = 3 : ui32, handshake.name = "br5"} : <i32>
    %28 = br %19 {handshake.bb = 3 : ui32, handshake.name = "br6"} : <i32>
    %29 = br %22 {handshake.bb = 3 : ui32, handshake.name = "br7"} : <i64>
    %30 = br %23 {handshake.bb = 3 : ui32, handshake.name = "br8"} : <i64>
    %31 = br %24 {handshake.bb = 3 : ui32, handshake.name = "br9"} : <i64>
    %32 = br %25 {handshake.bb = 3 : ui32, handshake.name = "br10"} : <i64>
    %33 = br %result_12 {handshake.bb = 3 : ui32, handshake.name = "br11"} : <>
    %34 = mux %index_15 [%26, %trueResult_22] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %35 = mux %index_15 [%27, %trueResult_24] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %36 = mux %index_15 [%28, %trueResult_26] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %37 = mux %index_15 [%29, %trueResult_28] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i64>, <i64>] to <i64>
    %38 = mux %index_15 [%30, %trueResult_30] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<i64>, <i64>] to <i64>
    %39 = mux %index_15 [%31, %trueResult_32] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %40 = mux %index_15 [%32, %trueResult_34] {handshake.bb = 4 : ui32, handshake.name = "mux9"} : <i1>, [<i64>, <i64>] to <i64>
    %result_14, %index_15 = control_merge [%33, %trueResult_36]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %41 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %42 = constant %41 {handshake.bb = 4 : ui32, handshake.name = "constant12", value = 20 : i32} : <>, <i32>
    %43 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %44 = constant %43 {handshake.bb = 4 : ui32, handshake.name = "constant13", value = 1 : i32} : <>, <i32>
    %45 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %46 = constant %45 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 4 : i64} : <>, <i64>
    %47 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %48 = constant %47 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 2 : i64} : <>, <i64>
    %49 = extui %34 {handshake.bb = 4 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %50 = shli %37, %48 {handshake.bb = 4 : ui32, handshake.name = "shli0"} : <i64>
    %51 = shli %37, %46 {handshake.bb = 4 : ui32, handshake.name = "shli1"} : <i64>
    %52 = addi %50, %51 {handshake.bb = 4 : ui32, handshake.name = "addi7"} : <i64>
    %53 = addi %52, %49 {handshake.bb = 4 : ui32, handshake.name = "addi2"} : <i64>
    %54 = trunci %53 {handshake.bb = 4 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%54] %0#0 {handshake.bb = 4 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %55 = trunci %38 {handshake.bb = 4 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_16, %dataResult_17 = load[%55] %outputs {handshake.bb = 4 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %56 = extui %34 {handshake.bb = 4 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %57 = shli %39, %48 {handshake.bb = 4 : ui32, handshake.name = "shli2"} : <i64>
    %58 = shli %39, %46 {handshake.bb = 4 : ui32, handshake.name = "shli3"} : <i64>
    %59 = addi %57, %58 {handshake.bb = 4 : ui32, handshake.name = "addi8"} : <i64>
    %60 = addi %59, %56 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i64>
    %61 = trunci %60 {handshake.bb = 4 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_18, %dataResult_19 = load[%61] %0#1 {handshake.bb = 4 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %62 = muli %dataResult_17, %dataResult_19 {handshake.bb = 4 : ui32, handshake.name = "muli2"} : <i32>
    %63 = subi %dataResult, %62 {handshake.bb = 4 : ui32, handshake.name = "subi0"} : <i32>
    %64 = extui %34 {handshake.bb = 4 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %65 = shli %40, %48 {handshake.bb = 4 : ui32, handshake.name = "shli4"} : <i64>
    %66 = shli %40, %46 {handshake.bb = 4 : ui32, handshake.name = "shli5"} : <i64>
    %67 = addi %65, %66 {handshake.bb = 4 : ui32, handshake.name = "addi9"} : <i64>
    %68 = addi %67, %64 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i64>
    %69 = trunci %68 {handshake.bb = 4 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_20, %dataResult_21 = store[%69] %63 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : <i32>, <i32>, <i32>, <i32>
    %70 = addi %34, %44 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i32>
    %71 = cmpi ult, %70, %42 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_22, %falseResult_23 = cond_br %71, %70 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %71, %35 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %71, %36 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %71, %37 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <i64>
    %trueResult_30, %falseResult_31 = cond_br %71, %38 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i64>
    %trueResult_32, %falseResult_33 = cond_br %71, %39 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <i64>
    %trueResult_34, %falseResult_35 = cond_br %71, %40 {handshake.bb = 4 : ui32, handshake.name = "cond_br16"} : <i1>, <i64>
    %trueResult_36, %falseResult_37 = cond_br %71, %result_14 {handshake.bb = 4 : ui32, handshake.name = "cond_br17"} : <i1>, <>
    %72 = mux %index_39 [%falseResult_1, %falseResult_9] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %result_38, %index_39 = control_merge [%falseResult_3, %falseResult_11]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %73 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %74 = constant %73 {handshake.bb = 5 : ui32, handshake.name = "constant16", value = 19 : i32} : <>, <i32>
    %75 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %76 = constant %75 {handshake.bb = 5 : ui32, handshake.name = "constant17", value = 1 : i32} : <>, <i32>
    %77 = addi %72, %76 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i32>
    %78 = cmpi ult, %77, %74 {handshake.bb = 5 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_40, %falseResult_41 = cond_br %78, %77 {handshake.bb = 5 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %78, %result_38 {handshake.bb = 5 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %result_44, %index_45 = control_merge [%falseResult_43]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    %79 = source {handshake.bb = 6 : ui32, handshake.name = "source10"} : <>
    %80 = constant %79 {handshake.bb = 6 : ui32, handshake.name = "constant18", value = 29070 : i32} : <>, <i32>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %80, %memEnd, %0#2, %arg4 : <i32>, <>, <>, <>
  }
}

