module {
  handshake.func @stencil_2d(%arg0: memref<900xi32>, %arg1: memref<10xi32>, %arg2: memref<900xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["orig", "filter", "sol", "orig_start", "filter_start", "sol_start", "start"], resNames = ["out0", "orig_end", "filter_end", "sol_end", "end"]} {
    %memEnd = mem_controller[%arg2 : memref<900xi32>] %arg5 (%66, %addressResult_33, %dataResult_34) %result_41 {connectedBlocks = [5 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<10xi32>] %arg4 (%addressResult) %result_41 {connectedBlocks = [3 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<900xi32>] %arg3 (%addressResult_7) %result_41 {connectedBlocks = [3 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %2 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %3 = mux %index [%1, %trueResult_35] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_37]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %4 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %5 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %6 = br %3 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %7 = br %result {handshake.bb = 1 : ui32, handshake.name = "br7"} : <>
    %8 = mux %index_4 [%5, %trueResult_23] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %9 = mux %index_4 [%5, %trueResult_25] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %index_4 [%6, %trueResult_27] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_3, %index_4 = control_merge [%7, %trueResult_29]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %11 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %12 = constant %11 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %13 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %14 = constant %13 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 3 : i32} : <>, <i32>
    %15 = constant %result_3 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 0 : i32} : <>, <i32>
    %16 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %17 = constant %16 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i32} : <>, <i32>
    %18 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %19 = constant %18 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 2 : i32} : <>, <i32>
    %20 = shli %8, %12 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i32>
    %21 = addi %8, %20 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i32>
    %22 = shli %8, %12 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i32>
    %23 = shli %8, %19 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i32>
    %24 = addi %22, %23 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i32>
    %25 = shli %8, %14 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i32>
    %26 = shli %8, %17 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i32>
    %27 = addi %25, %26 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i32>
    %28 = addi %24, %27 {handshake.bb = 2 : ui32, handshake.name = "addi10"} : <i32>
    %29 = addi %28, %10 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %30 = br %15 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <i32>
    %31 = br %9 {handshake.bb = 2 : ui32, handshake.name = "br9"} : <i32>
    %32 = br %10 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <i32>
    %33 = br %8 {handshake.bb = 2 : ui32, handshake.name = "br11"} : <i32>
    %34 = br %21 {handshake.bb = 2 : ui32, handshake.name = "br12"} : <i32>
    %35 = br %29 {handshake.bb = 2 : ui32, handshake.name = "br13"} : <i32>
    %36 = br %result_3 {handshake.bb = 2 : ui32, handshake.name = "br14"} : <>
    %37 = mux %index_6 [%30, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %38 = mux %index_6 [%31, %trueResult_9] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %39 = mux %index_6 [%32, %trueResult_11] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %40 = mux %index_6 [%33, %trueResult_13] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %41 = mux %index_6 [%34, %trueResult_15] {handshake.bb = 3 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %42 = mux %index_6 [%35, %trueResult_17] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %result_5, %index_6 = control_merge [%36, %trueResult_19]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %43 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %44 = constant %43 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 1 : i32} : <>, <i32>
    %45 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %46 = constant %45 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 3 : i32} : <>, <i32>
    %47 = addi %41, %37 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i32>
    %48 = extui %47 {handshake.bb = 3 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %49 = trunci %48 {handshake.bb = 3 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%49] %outputs {handshake.bb = 3 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %50 = addi %42, %37 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %51 = extui %50 {handshake.bb = 3 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %52 = trunci %51 {handshake.bb = 3 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_7, %dataResult_8 = load[%52] %outputs_1 {handshake.bb = 3 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %53 = muli %dataResult, %dataResult_8 {handshake.bb = 3 : ui32, handshake.name = "muli2"} : <i32>
    %54 = addi %38, %53 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %55 = addi %37, %44 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i32>
    %56 = cmpi ult, %55, %46 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %56, %55 {handshake.bb = 3 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_9, %falseResult_10 = cond_br %56, %54 {handshake.bb = 3 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %56, %39 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_13, %falseResult_14 = cond_br %56, %40 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_15, %falseResult_16 = cond_br %56, %41 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_17, %falseResult_18 = cond_br %56, %42 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_19, %falseResult_20 = cond_br %56, %result_5 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %57 = merge %falseResult_10 {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i32>
    %58 = merge %falseResult_12 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <i32>
    %59 = merge %falseResult_14 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i32>
    %result_21, %index_22 = control_merge [%falseResult_20]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    %60 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %61 = constant %60 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %62 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %63 = constant %62 {handshake.bb = 4 : ui32, handshake.name = "constant16", value = 3 : i32} : <>, <i32>
    %64 = addi %59, %61 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i32>
    %65 = cmpi ult, %64, %63 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_23, %falseResult_24 = cond_br %65, %64 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_25, %falseResult_26 = cond_br %65, %57 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_27, %falseResult_28 = cond_br %65, %58 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_29, %falseResult_30 = cond_br %65, %result_21 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %66 = constant %result_31 {handshake.bb = 5 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %67 = merge %falseResult_26 {handshake.bb = 5 : ui32, handshake.name = "merge3"} : <i32>
    %68 = merge %falseResult_28 {handshake.bb = 5 : ui32, handshake.name = "merge4"} : <i32>
    %result_31, %index_32 = control_merge [%falseResult_30]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %69 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %70 = constant %69 {handshake.bb = 5 : ui32, handshake.name = "constant17", value = 28 : i32} : <>, <i32>
    %71 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %72 = constant %71 {handshake.bb = 5 : ui32, handshake.name = "constant18", value = 1 : i32} : <>, <i32>
    %73 = extui %68 {handshake.bb = 5 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %74 = trunci %73 {handshake.bb = 5 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_33, %dataResult_34 = store[%74] %67 {handshake.bb = 5 : ui32, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %75 = addi %68, %72 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i32>
    %76 = cmpi ult, %75, %70 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_35, %falseResult_36 = cond_br %76, %75 {handshake.bb = 5 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_37, %falseResult_38 = cond_br %76, %result_31 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %trueResult_39, %falseResult_40 = cond_br %76, %67 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %77 = merge %falseResult_40 {handshake.bb = 6 : ui32, handshake.name = "merge5"} : <i32>
    %result_41, %index_42 = control_merge [%falseResult_38]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %77, %memEnd_2, %memEnd_0, %memEnd, %arg6 : <i32>, <>, <>, <>, <>
  }
}

