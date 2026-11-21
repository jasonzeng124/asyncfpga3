module {
  handshake.func @matrix(%arg0: memref<900xi32>, %arg1: memref<900xi32>, %arg2: memref<900xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["inA", "inB", "outC", "inA_start", "inB_start", "outC_start", "start"], resNames = ["inA_end", "inB_end", "outC_end", "end"]} {
    %memEnd = mem_controller[%arg2 : memref<900xi32>] %arg5 (%68, %addressResult_25, %dataResult_26) %result_43 {connectedBlocks = [4 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<900xi32>] %arg4 (%addressResult_7) %result_43 {connectedBlocks = [3 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<900xi32>] %arg3 (%addressResult) %result_43 {connectedBlocks = [3 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %2 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %3 = mux %index [%1, %trueResult_39] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_41]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %4 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %5 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %6 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %7 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %8 = br %3 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %9 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i64>
    %10 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i64>
    %11 = br %result {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %12 = mux %index_4 [%7, %trueResult_27] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %13 = mux %index_4 [%8, %trueResult_29] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %14 = mux %index_4 [%9, %trueResult_31] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i64>, <i64>] to <i64>
    %15 = mux %index_4 [%10, %trueResult_33] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %result_3, %index_4 = control_merge [%11, %trueResult_35]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %16 = constant %result_3 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %17 = extui %12 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %18 = br %16 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <i32>
    %19 = br %13 {handshake.bb = 2 : ui32, handshake.name = "br11"} : <i32>
    %20 = br %14 {handshake.bb = 2 : ui32, handshake.name = "br12"} : <i64>
    %21 = br %15 {handshake.bb = 2 : ui32, handshake.name = "br13"} : <i64>
    %22 = br %12 {handshake.bb = 2 : ui32, handshake.name = "br14"} : <i32>
    %23 = br %17 {handshake.bb = 2 : ui32, handshake.name = "br15"} : <i64>
    %24 = br %result_3 {handshake.bb = 2 : ui32, handshake.name = "br16"} : <>
    %25 = mux %index_6 [%18, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %26 = mux %index_6 [%18, %trueResult_9] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %27 = mux %index_6 [%19, %trueResult_11] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %28 = mux %index_6 [%20, %trueResult_13] {handshake.bb = 3 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %29 = mux %index_6 [%21, %trueResult_15] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i64>, <i64>] to <i64>
    %30 = mux %index_6 [%22, %trueResult_17] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %31 = mux %index_6 [%23, %trueResult_19] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i64>, <i64>] to <i64>
    %result_5, %index_6 = control_merge [%24, %trueResult_21]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %32 = source {handshake.bb = 3 : ui32, handshake.name = "source0"} : <>
    %33 = constant %32 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 30 : i32} : <>, <i32>
    %34 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %35 = constant %34 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 1 : i32} : <>, <i32>
    %36 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %37 = constant %36 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 4 : i64} : <>, <i64>
    %38 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %39 = constant %38 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 3 : i64} : <>, <i64>
    %40 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %41 = constant %40 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 2 : i64} : <>, <i64>
    %42 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %43 = constant %42 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 1 : i64} : <>, <i64>
    %44 = extui %25 {handshake.bb = 3 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %45 = shli %28, %43 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i64>
    %46 = shli %28, %41 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i64>
    %47 = addi %45, %46 {handshake.bb = 3 : ui32, handshake.name = "addi7"} : <i64>
    %48 = shli %28, %39 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i64>
    %49 = shli %28, %37 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i64>
    %50 = addi %48, %49 {handshake.bb = 3 : ui32, handshake.name = "addi8"} : <i64>
    %51 = addi %47, %50 {handshake.bb = 3 : ui32, handshake.name = "addi9"} : <i64>
    %52 = addi %51, %44 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i64>
    %53 = trunci %52 {handshake.bb = 3 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%53] %outputs_1 {handshake.bb = 3 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %54 = extui %25 {handshake.bb = 3 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %55 = shli %54, %43 {handshake.bb = 3 : ui32, handshake.name = "shli4"} : <i64>
    %56 = shli %54, %41 {handshake.bb = 3 : ui32, handshake.name = "shli5"} : <i64>
    %57 = addi %55, %56 {handshake.bb = 3 : ui32, handshake.name = "addi10"} : <i64>
    %58 = shli %54, %39 {handshake.bb = 3 : ui32, handshake.name = "shli6"} : <i64>
    %59 = shli %54, %37 {handshake.bb = 3 : ui32, handshake.name = "shli7"} : <i64>
    %60 = addi %58, %59 {handshake.bb = 3 : ui32, handshake.name = "addi11"} : <i64>
    %61 = addi %57, %60 {handshake.bb = 3 : ui32, handshake.name = "addi12"} : <i64>
    %62 = addi %61, %31 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i64>
    %63 = trunci %62 {handshake.bb = 3 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_7, %dataResult_8 = load[%63] %outputs {handshake.bb = 3 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %64 = muli %dataResult, %dataResult_8 {handshake.bb = 3 : ui32, handshake.name = "muli2"} : <i32>
    %65 = addi %26, %64 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %66 = addi %25, %35 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %67 = cmpi ult, %66, %33 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %67, %66 {handshake.bb = 3 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_9, %falseResult_10 = cond_br %67, %65 {handshake.bb = 3 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %67, %27 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_13, %falseResult_14 = cond_br %67, %28 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i64>
    %trueResult_15, %falseResult_16 = cond_br %67, %29 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i64>
    %trueResult_17, %falseResult_18 = cond_br %67, %30 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_19, %falseResult_20 = cond_br %67, %31 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i64>
    %trueResult_21, %falseResult_22 = cond_br %67, %result_5 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %68 = constant %result_23 {handshake.bb = 4 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %69 = merge %falseResult_10 {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i32>
    %70 = merge %falseResult_12 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <i32>
    %71 = merge %falseResult_14 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i64>
    %72 = merge %falseResult_16 {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <i64>
    %73 = merge %falseResult_18 {handshake.bb = 4 : ui32, handshake.name = "merge4"} : <i32>
    %result_23, %index_24 = control_merge [%falseResult_22]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    %74 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %75 = constant %74 {handshake.bb = 4 : ui32, handshake.name = "constant16", value = 30 : i32} : <>, <i32>
    %76 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %77 = constant %76 {handshake.bb = 4 : ui32, handshake.name = "constant17", value = 1 : i32} : <>, <i32>
    %78 = source {handshake.bb = 4 : ui32, handshake.name = "source8"} : <>
    %79 = constant %78 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 4 : i64} : <>, <i64>
    %80 = source {handshake.bb = 4 : ui32, handshake.name = "source9"} : <>
    %81 = constant %80 {handshake.bb = 4 : ui32, handshake.name = "constant19", value = 3 : i64} : <>, <i64>
    %82 = source {handshake.bb = 4 : ui32, handshake.name = "source10"} : <>
    %83 = constant %82 {handshake.bb = 4 : ui32, handshake.name = "constant20", value = 2 : i64} : <>, <i64>
    %84 = source {handshake.bb = 4 : ui32, handshake.name = "source11"} : <>
    %85 = constant %84 {handshake.bb = 4 : ui32, handshake.name = "constant21", value = 1 : i64} : <>, <i64>
    %86 = extui %73 {handshake.bb = 4 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %87 = shli %72, %85 {handshake.bb = 4 : ui32, handshake.name = "shli8"} : <i64>
    %88 = shli %72, %83 {handshake.bb = 4 : ui32, handshake.name = "shli9"} : <i64>
    %89 = addi %87, %88 {handshake.bb = 4 : ui32, handshake.name = "addi13"} : <i64>
    %90 = shli %72, %81 {handshake.bb = 4 : ui32, handshake.name = "shli10"} : <i64>
    %91 = shli %72, %79 {handshake.bb = 4 : ui32, handshake.name = "shli11"} : <i64>
    %92 = addi %90, %91 {handshake.bb = 4 : ui32, handshake.name = "addi14"} : <i64>
    %93 = addi %89, %92 {handshake.bb = 4 : ui32, handshake.name = "addi15"} : <i64>
    %94 = addi %93, %86 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i64>
    %95 = trunci %94 {handshake.bb = 4 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_25, %dataResult_26 = store[%95] %69 {handshake.bb = 4 : ui32, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %96 = addi %73, %77 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i32>
    %97 = cmpi ult, %96, %75 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_27, %falseResult_28 = cond_br %97, %96 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_29, %falseResult_30 = cond_br %97, %70 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_31, %falseResult_32 = cond_br %97, %71 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <i64>
    %trueResult_33, %falseResult_34 = cond_br %97, %72 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i64>
    %trueResult_35, %falseResult_36 = cond_br %97, %result_23 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %98 = merge %falseResult_30 {handshake.bb = 5 : ui32, handshake.name = "merge5"} : <i32>
    %result_37, %index_38 = control_merge [%falseResult_36]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %99 = source {handshake.bb = 5 : ui32, handshake.name = "source12"} : <>
    %100 = constant %99 {handshake.bb = 5 : ui32, handshake.name = "constant22", value = 30 : i32} : <>, <i32>
    %101 = source {handshake.bb = 5 : ui32, handshake.name = "source13"} : <>
    %102 = constant %101 {handshake.bb = 5 : ui32, handshake.name = "constant23", value = 1 : i32} : <>, <i32>
    %103 = addi %98, %102 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i32>
    %104 = cmpi ult, %103, %100 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_39, %falseResult_40 = cond_br %104, %103 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_41, %falseResult_42 = cond_br %104, %result_37 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <>
    %result_43, %index_44 = control_merge [%falseResult_42]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %memEnd_2, %memEnd_0, %memEnd, %arg6 : <>, <>, <>, <>
  }
}

