module {
  handshake.func @mvt_float(%arg0: memref<900xf32>, %arg1: memref<30xf32>, %arg2: memref<30xf32>, %arg3: memref<30xf32>, %arg4: memref<30xf32>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "x1", "x2", "y1", "y2", "A_start", "x1_start", "x2_start", "y1_start", "y2_start", "start"], resNames = ["A_end", "x1_end", "x2_end", "y1_end", "y2_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg4 : memref<30xf32>] %arg9 (%addressResult_40) %result_60 {connectedBlocks = [5 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_0, %memEnd_1 = mem_controller[%arg3 : memref<30xf32>] %arg8 (%addressResult_12) %result_60 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_2, %memEnd_3 = mem_controller[%arg2 : memref<30xf32>] %arg7 (%addressResult_34, %99, %addressResult_54, %dataResult_55) %result_60 {connectedBlocks = [4 : i32, 6 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>) -> !handshake.channel<f32>
    %outputs_4, %memEnd_5 = mem_controller[%arg1 : memref<30xf32>] %arg6 (%addressResult, %45, %addressResult_24, %dataResult_25) %result_60 {connectedBlocks = [1 : i32, 3 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>) -> !handshake.channel<f32>
    %outputs_6:2, %memEnd_7 = mem_controller[%arg0 : memref<900xf32>] %arg5 (%addressResult_10, %addressResult_38) %result_60 {connectedBlocks = [2 : i32, 5 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %0 = constant %arg10 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %2 = br %arg10 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %3 = mux %index [%1, %trueResult_26] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_28]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %4 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %5 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %6 = trunci %5 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%6] %outputs_4 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %7 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %8 = br %dataResult {handshake.bb = 1 : ui32, handshake.name = "br5"} : <f32>
    %9 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %10 = br %3 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i32>
    %11 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i64>
    %12 = br %result {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %13 = mux %index_9 [%8, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %14 = mux %index_9 [%9, %trueResult_14] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %15 = mux %index_9 [%10, %trueResult_16] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %index_9 [%11, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %result_8, %index_9 = control_merge [%12, %trueResult_20]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %17 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %18 = constant %17 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 30 : i32} : <>, <i32>
    %19 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %20 = constant %19 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 3 : i64} : <>, <i64>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 2 : i64} : <>, <i64>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %28 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i64} : <>, <i64>
    %29 = extui %14 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %30 = shli %16, %28 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %31 = shli %16, %26 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %32 = addi %30, %31 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i64>
    %33 = shli %16, %24 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %34 = shli %16, %22 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %35 = addi %33, %34 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i64>
    %36 = addi %32, %35 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i64>
    %37 = addi %36, %29 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %38 = trunci %37 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_10, %dataResult_11 = load[%38] %outputs_6#0 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <f32>, <i32>, <f32>
    %39 = extui %14 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %40 = trunci %39 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = load[%40] %outputs_0 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <f32>, <i32>, <f32>
    %41 = mulf %dataResult_11, %dataResult_13 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %42 = addf %13, %41 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf0"} : <f32>
    %43 = addi %14, %20 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %44 = cmpi ult, %43, %18 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %44, %42 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <f32>
    %trueResult_14, %falseResult_15 = cond_br %44, %43 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %44, %15 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %44, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i64>
    %trueResult_20, %falseResult_21 = cond_br %44, %result_8 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %45 = constant %result_22 {handshake.bb = 3 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %46 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <f32>
    %47 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %result_22, %index_23 = control_merge [%falseResult_21]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %48 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %49 = constant %48 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 30 : i32} : <>, <i32>
    %50 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %51 = constant %50 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 1 : i32} : <>, <i32>
    %52 = constant %result_22 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 0 : i32} : <>, <i32>
    %53 = extui %47 {handshake.bb = 3 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %54 = trunci %53 {handshake.bb = 3 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_24, %dataResult_25 = store[%54] %46 {handshake.bb = 3 : ui32, handshake.name = "store3"} : <i32>, <f32>, <i32>, <f32>
    %55 = addi %47, %51 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %56 = cmpi ult, %55, %49 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %56, %55 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %56, %result_22 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %trueResult_30, %falseResult_31 = cond_br %56, %52 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %57 = mux %index_33 [%falseResult_31, %trueResult_56] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_32, %index_33 = control_merge [%falseResult_29, %trueResult_58]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %58 = constant %result_32 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 0 : i32} : <>, <i32>
    %59 = extui %57 {handshake.bb = 4 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %60 = trunci %59 {handshake.bb = 4 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_34, %dataResult_35 = load[%60] %outputs_2 {handshake.bb = 4 : ui32, handshake.name = "load4"} : <i32>, <f32>, <i32>, <f32>
    %61 = extui %57 {handshake.bb = 4 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %62 = br %dataResult_35 {handshake.bb = 4 : ui32, handshake.name = "br10"} : <f32>
    %63 = br %58 {handshake.bb = 4 : ui32, handshake.name = "br11"} : <i32>
    %64 = br %57 {handshake.bb = 4 : ui32, handshake.name = "br12"} : <i32>
    %65 = br %61 {handshake.bb = 4 : ui32, handshake.name = "br13"} : <i64>
    %66 = br %result_32 {handshake.bb = 4 : ui32, handshake.name = "br14"} : <>
    %67 = mux %index_37 [%62, %trueResult_42] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<f32>, <f32>] to <f32>
    %68 = mux %index_37 [%63, %trueResult_44] {handshake.bb = 5 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %69 = mux %index_37 [%64, %trueResult_46] {handshake.bb = 5 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %70 = mux %index_37 [%65, %trueResult_48] {handshake.bb = 5 : ui32, handshake.name = "mux9"} : <i1>, [<i64>, <i64>] to <i64>
    %result_36, %index_37 = control_merge [%66, %trueResult_50]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %71 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %72 = constant %71 {handshake.bb = 5 : ui32, handshake.name = "constant19", value = 30 : i32} : <>, <i32>
    %73 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %74 = constant %73 {handshake.bb = 5 : ui32, handshake.name = "constant20", value = 1 : i32} : <>, <i32>
    %75 = source {handshake.bb = 5 : ui32, handshake.name = "source10"} : <>
    %76 = constant %75 {handshake.bb = 5 : ui32, handshake.name = "constant21", value = 4 : i64} : <>, <i64>
    %77 = source {handshake.bb = 5 : ui32, handshake.name = "source11"} : <>
    %78 = constant %77 {handshake.bb = 5 : ui32, handshake.name = "constant22", value = 3 : i64} : <>, <i64>
    %79 = source {handshake.bb = 5 : ui32, handshake.name = "source12"} : <>
    %80 = constant %79 {handshake.bb = 5 : ui32, handshake.name = "constant23", value = 2 : i64} : <>, <i64>
    %81 = source {handshake.bb = 5 : ui32, handshake.name = "source13"} : <>
    %82 = constant %81 {handshake.bb = 5 : ui32, handshake.name = "constant24", value = 1 : i64} : <>, <i64>
    %83 = extui %68 {handshake.bb = 5 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %84 = shli %83, %82 {handshake.bb = 5 : ui32, handshake.name = "shli4"} : <i64>
    %85 = shli %83, %80 {handshake.bb = 5 : ui32, handshake.name = "shli5"} : <i64>
    %86 = addi %84, %85 {handshake.bb = 5 : ui32, handshake.name = "addi9"} : <i64>
    %87 = shli %83, %78 {handshake.bb = 5 : ui32, handshake.name = "shli6"} : <i64>
    %88 = shli %83, %76 {handshake.bb = 5 : ui32, handshake.name = "shli7"} : <i64>
    %89 = addi %87, %88 {handshake.bb = 5 : ui32, handshake.name = "addi10"} : <i64>
    %90 = addi %86, %89 {handshake.bb = 5 : ui32, handshake.name = "addi11"} : <i64>
    %91 = addi %90, %70 {handshake.bb = 5 : ui32, handshake.name = "addi3"} : <i64>
    %92 = trunci %91 {handshake.bb = 5 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_38, %dataResult_39 = load[%92] %outputs_6#1 {handshake.bb = 5 : ui32, handshake.name = "load5"} : <i32>, <f32>, <i32>, <f32>
    %93 = extui %68 {handshake.bb = 5 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %94 = trunci %93 {handshake.bb = 5 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_40, %dataResult_41 = load[%94] %outputs {handshake.bb = 5 : ui32, handshake.name = "load6"} : <i32>, <f32>, <i32>, <f32>
    %95 = mulf %dataResult_39, %dataResult_41 {fastmath = #arith.fastmath<none>, handshake.bb = 5 : ui32, handshake.name = "mulf1"} : <f32>
    %96 = addf %67, %95 {fastmath = #arith.fastmath<none>, handshake.bb = 5 : ui32, handshake.name = "addf1"} : <f32>
    %97 = addi %68, %74 {handshake.bb = 5 : ui32, handshake.name = "addi4"} : <i32>
    %98 = cmpi ult, %97, %72 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_42, %falseResult_43 = cond_br %98, %96 {handshake.bb = 5 : ui32, handshake.name = "cond_br12"} : <i1>, <f32>
    %trueResult_44, %falseResult_45 = cond_br %98, %97 {handshake.bb = 5 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_46, %falseResult_47 = cond_br %98, %69 {handshake.bb = 5 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_48, %falseResult_49 = cond_br %98, %70 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <i64>
    %trueResult_50, %falseResult_51 = cond_br %98, %result_36 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %99 = constant %result_52 {handshake.bb = 6 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %100 = merge %falseResult_43 {handshake.bb = 6 : ui32, handshake.name = "merge2"} : <f32>
    %101 = merge %falseResult_47 {handshake.bb = 6 : ui32, handshake.name = "merge3"} : <i32>
    %result_52, %index_53 = control_merge [%falseResult_51]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    %102 = source {handshake.bb = 6 : ui32, handshake.name = "source14"} : <>
    %103 = constant %102 {handshake.bb = 6 : ui32, handshake.name = "constant25", value = 30 : i32} : <>, <i32>
    %104 = source {handshake.bb = 6 : ui32, handshake.name = "source15"} : <>
    %105 = constant %104 {handshake.bb = 6 : ui32, handshake.name = "constant26", value = 1 : i32} : <>, <i32>
    %106 = extui %101 {handshake.bb = 6 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %107 = trunci %106 {handshake.bb = 6 : ui32, handshake.name = "index_cast7"} : <i64> to <i32>
    %addressResult_54, %dataResult_55 = store[%107] %100 {handshake.bb = 6 : ui32, handshake.name = "store7"} : <i32>, <f32>, <i32>, <f32>
    %108 = addi %101, %105 {handshake.bb = 6 : ui32, handshake.name = "addi5"} : <i32>
    %109 = cmpi ult, %108, %103 {handshake.bb = 6 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_56, %falseResult_57 = cond_br %109, %108 {handshake.bb = 6 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_58, %falseResult_59 = cond_br %109, %result_52 {handshake.bb = 6 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %result_60, %index_61 = control_merge [%falseResult_59]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    end {handshake.bb = 7 : ui32, handshake.name = "end0"} %memEnd_7, %memEnd_5, %memEnd_3, %memEnd_1, %memEnd, %arg10 : <>, <>, <>, <>, <>, <>
  }
}

