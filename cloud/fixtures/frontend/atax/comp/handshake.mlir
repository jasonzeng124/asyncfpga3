module {
  handshake.func @atax(%arg0: memref<400xi32>, %arg1: memref<20xi32>, %arg2: memref<20xi32>, %arg3: memref<20xi32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "x", "y", "tmp", "A_start", "x_start", "y_start", "tmp_start", "start"], resNames = ["A_end", "x_end", "y_end", "tmp_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg3 : memref<20xi32>] %arg7 (%addressResult, %73, %addressResult_40, %dataResult_41) %result_46 {connectedBlocks = [1 : i32, 5 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0:2 = lsq[%arg2 : memref<20xi32>] (%arg6, %result_20, %addressResult_22, %addressResult_26, %dataResult_27, %result_46)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %outputs_0, %memEnd_1 = mem_controller[%arg1 : memref<20xi32>] %arg5 (%addressResult_8) %result_46 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_2:2, %memEnd_3 = mem_controller[%arg0 : memref<400xi32>] %arg4 (%addressResult_6, %addressResult_24) %result_46 {connectedBlocks = [2 : i32, 4 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %1 = constant %arg8 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %3 = br %arg8 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %4 = mux %index [%2, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %6 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %7 = trunci %6 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%7] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %8 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %9 = br %dataResult {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %10 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %11 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i32>
    %12 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i64>
    %13 = br %result {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %14 = mux %index_5 [%9, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %15 = mux %index_5 [%10, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %index_5 [%11, %trueResult_12] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_5 [%12, %trueResult_14] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %result_4, %index_5 = control_merge [%13, %trueResult_16]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %18 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %19 = constant %18 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 20 : i32} : <>, <i32>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %23 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 4 : i64} : <>, <i64>
    %24 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %25 = constant %24 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 2 : i64} : <>, <i64>
    %26 = extui %15 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %27 = shli %17, %25 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %28 = shli %17, %23 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %29 = addi %27, %28 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i64>
    %30 = addi %29, %26 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %31 = trunci %30 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_6, %dataResult_7 = load[%31] %outputs_2#0 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %32 = extui %15 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %33 = trunci %32 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_8, %dataResult_9 = load[%33] %outputs_0 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %34 = muli %dataResult_7, %dataResult_9 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %35 = addi %14, %34 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %36 = addi %15, %21 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %37 = cmpi ult, %36, %19 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %37, %35 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %37, %36 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %37, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %37, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i64>
    %trueResult_16, %falseResult_17 = cond_br %37, %result_4 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %38 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %39 = merge %falseResult_13 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %result_18, %index_19 = control_merge [%falseResult_17]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %40 = constant %result_18 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 0 : i32} : <>, <i32>
    %41 = extui %39 {handshake.bb = 3 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %42 = br %40 {handshake.bb = 3 : ui32, handshake.name = "br10"} : <i32>
    %43 = br %39 {handshake.bb = 3 : ui32, handshake.name = "br11"} : <i32>
    %44 = br %38 {handshake.bb = 3 : ui32, handshake.name = "br12"} : <i32>
    %45 = br %41 {handshake.bb = 3 : ui32, handshake.name = "br13"} : <i64>
    %46 = br %result_18 {handshake.bb = 3 : ui32, handshake.name = "br14"} : <>
    %47 = mux %index_21 [%42, %trueResult_28] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %48 = mux %index_21 [%43, %trueResult_30] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %49 = mux %index_21 [%44, %trueResult_32] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %50 = mux %index_21 [%45, %trueResult_34] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %result_20, %index_21 = control_merge [%46, %trueResult_36]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %51 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %52 = constant %51 {handshake.bb = 4 : ui32, handshake.name = "constant12", value = 20 : i32} : <>, <i32>
    %53 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %54 = constant %53 {handshake.bb = 4 : ui32, handshake.name = "constant13", value = 1 : i32} : <>, <i32>
    %55 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %56 = constant %55 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 4 : i64} : <>, <i64>
    %57 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %58 = constant %57 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 2 : i64} : <>, <i64>
    %59 = extui %47 {handshake.bb = 4 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %60 = trunci %59 {handshake.bb = 4 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_22, %dataResult_23 = load[%60] %0#0 {handshake.bb = 4 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %61 = extui %47 {handshake.bb = 4 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %62 = shli %50, %58 {handshake.bb = 4 : ui32, handshake.name = "shli2"} : <i64>
    %63 = shli %50, %56 {handshake.bb = 4 : ui32, handshake.name = "shli3"} : <i64>
    %64 = addi %62, %63 {handshake.bb = 4 : ui32, handshake.name = "addi8"} : <i64>
    %65 = addi %64, %61 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i64>
    %66 = trunci %65 {handshake.bb = 4 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_24, %dataResult_25 = load[%66] %outputs_2#1 {handshake.bb = 4 : ui32, handshake.name = "load4"} : <i32>, <i32>, <i32>, <i32>
    %67 = muli %dataResult_25, %49 {handshake.bb = 4 : ui32, handshake.name = "muli3"} : <i32>
    %68 = addi %dataResult_23, %67 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i32>
    %69 = extui %47 {handshake.bb = 4 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %70 = trunci %69 {handshake.bb = 4 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_26, %dataResult_27 = store[%70] %68 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %71 = addi %47, %54 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i32>
    %72 = cmpi ult, %71, %52 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_28, %falseResult_29 = cond_br %72, %71 {handshake.bb = 4 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %72, %48 {handshake.bb = 4 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %72, %49 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_34, %falseResult_35 = cond_br %72, %50 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i64>
    %trueResult_36, %falseResult_37 = cond_br %72, %result_20 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %73 = constant %result_38 {handshake.bb = 5 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %74 = merge %falseResult_31 {handshake.bb = 5 : ui32, handshake.name = "merge2"} : <i32>
    %75 = merge %falseResult_33 {handshake.bb = 5 : ui32, handshake.name = "merge3"} : <i32>
    %result_38, %index_39 = control_merge [%falseResult_37]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %76 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %77 = constant %76 {handshake.bb = 5 : ui32, handshake.name = "constant16", value = 20 : i32} : <>, <i32>
    %78 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %79 = constant %78 {handshake.bb = 5 : ui32, handshake.name = "constant17", value = 1 : i32} : <>, <i32>
    %80 = extui %74 {handshake.bb = 5 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %81 = trunci %80 {handshake.bb = 5 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_40, %dataResult_41 = store[%81] %75 {handshake.bb = 5 : ui32, handshake.name = "store6"} : <i32>, <i32>, <i32>, <i32>
    %82 = addi %74, %79 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i32>
    %83 = cmpi ult, %82, %77 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_42, %falseResult_43 = cond_br %83, %82 {handshake.bb = 5 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_44, %falseResult_45 = cond_br %83, %result_38 {handshake.bb = 5 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %result_46, %index_47 = control_merge [%falseResult_45]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %memEnd_3, %memEnd_1, %0#1, %memEnd, %arg8 : <>, <>, <>, <>, <>
  }
}

