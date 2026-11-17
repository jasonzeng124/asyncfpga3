module {
  handshake.func @float_basic(%arg0: memref<900xf32>, %arg1: memref<900xf32>, %arg2: memref<30xf32>, %arg3: memref<30xf32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "y", "x", "A_start", "B_start", "y_start", "x_start", "start"], resNames = ["A_end", "B_end", "y_end", "x_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg3 : memref<30xf32>] %arg7 (%addressResult) %result_53 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %memEnd_0 = mem_controller[%arg2 : memref<30xf32>] %arg6 (%127, %addressResult_47, %dataResult_48) %result_53 {connectedBlocks = [6 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>) -> ()
    %outputs_1:2, %memEnd_2 = mem_controller[%arg1 : memref<900xf32>] %arg5 (%addressResult_9, %addressResult_29) %result_53 {connectedBlocks = [2 : i32, 4 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %outputs_3:2, %memEnd_4 = mem_controller[%arg0 : memref<900xf32>] %arg4 (%addressResult_7, %addressResult_25) %result_53 {connectedBlocks = [2 : i32, 3 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %0 = constant %arg8 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %2 = br %arg8 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <>
    %3 = mux %index [%1, %trueResult_49] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_51]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %4 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 0.000000e+00 : f32} : <>, <f32>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 0 : i32} : <>, <i32>
    %6 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %7 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %8 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <f32>
    %9 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i32>
    %10 = br %3 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i32>
    %11 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i64>
    %12 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <i64>
    %13 = br %result {handshake.bb = 1 : ui32, handshake.name = "br11"} : <>
    %14 = mux %index_6 [%8, %trueResult_33] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %15 = mux %index_6 [%9, %trueResult_35] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %index_6 [%10, %trueResult_37] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_6 [%11, %trueResult_39] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %18 = mux %index_6 [%12, %trueResult_41] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i64>, <i64>] to <i64>
    %result_5, %index_6 = control_merge [%13, %trueResult_43]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %19 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %20 = constant %19 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 3 : i64} : <>, <i64>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 2 : i64} : <>, <i64>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i64} : <>, <i64>
    %27 = extui %15 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %28 = trunci %27 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%28] %outputs {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %29 = extui %15 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %30 = shli %17, %26 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %31 = shli %17, %24 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %32 = addi %30, %31 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i64>
    %33 = shli %17, %22 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %34 = shli %17, %20 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %35 = addi %33, %34 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i64>
    %36 = addi %32, %35 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i64>
    %37 = addi %36, %29 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %38 = trunci %37 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_7, %dataResult_8 = load[%38] %outputs_3#0 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <f32>, <i32>, <f32>
    %39 = extui %15 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %40 = shli %18, %26 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i64>
    %41 = shli %18, %24 {handshake.bb = 2 : ui32, handshake.name = "shli5"} : <i64>
    %42 = addi %40, %41 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i64>
    %43 = shli %18, %22 {handshake.bb = 2 : ui32, handshake.name = "shli6"} : <i64>
    %44 = shli %18, %20 {handshake.bb = 2 : ui32, handshake.name = "shli7"} : <i64>
    %45 = addi %43, %44 {handshake.bb = 2 : ui32, handshake.name = "addi10"} : <i64>
    %46 = addi %42, %45 {handshake.bb = 2 : ui32, handshake.name = "addi11"} : <i64>
    %47 = addi %46, %39 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i64>
    %48 = trunci %47 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_9, %dataResult_10 = load[%48] %outputs_1#0 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <f32>, <i32>, <f32>
    %49 = cmpf ugt, %dataResult_8, %dataResult_10 {handshake.bb = 2 : ui32, handshake.name = "cmpf0"} : <f32>
    %trueResult, %falseResult = cond_br %49, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %49, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i64>
    %trueResult_13, %falseResult_14 = cond_br %49, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i64>
    %trueResult_15, %falseResult_16 = cond_br %49, %14 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %trueResult_17, %falseResult_18 = cond_br %49, %15 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_19, %falseResult_20 = cond_br %49, %dataResult {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <f32>
    %trueResult_21, %falseResult_22 = cond_br %49, %result_5 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %50 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %51 = merge %falseResult_12 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i64>
    %52 = merge %falseResult_14 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i64>
    %53 = merge %falseResult_16 {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <f32>
    %54 = merge %falseResult_18 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i32>
    %55 = merge %falseResult_20 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <f32>
    %result_23, %index_24 = control_merge [%falseResult_22]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %56 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %57 = constant %56 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 4 : i64} : <>, <i64>
    %58 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %59 = constant %58 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 3 : i64} : <>, <i64>
    %60 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %61 = constant %60 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 2 : i64} : <>, <i64>
    %62 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %63 = constant %62 {handshake.bb = 3 : ui32, handshake.name = "constant18", value = 1 : i64} : <>, <i64>
    %64 = extui %50 {handshake.bb = 3 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %65 = extui %54 {handshake.bb = 3 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %66 = shli %64, %63 {handshake.bb = 3 : ui32, handshake.name = "shli8"} : <i64>
    %67 = shli %64, %61 {handshake.bb = 3 : ui32, handshake.name = "shli9"} : <i64>
    %68 = addi %66, %67 {handshake.bb = 3 : ui32, handshake.name = "addi12"} : <i64>
    %69 = shli %64, %59 {handshake.bb = 3 : ui32, handshake.name = "shli10"} : <i64>
    %70 = shli %64, %57 {handshake.bb = 3 : ui32, handshake.name = "shli11"} : <i64>
    %71 = addi %69, %70 {handshake.bb = 3 : ui32, handshake.name = "addi13"} : <i64>
    %72 = addi %68, %71 {handshake.bb = 3 : ui32, handshake.name = "addi14"} : <i64>
    %73 = addi %72, %65 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i64>
    %74 = trunci %73 {handshake.bb = 3 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_25, %dataResult_26 = load[%74] %outputs_3#1 {handshake.bb = 3 : ui32, handshake.name = "load3"} : <i32>, <f32>, <i32>, <f32>
    %75 = divf %dataResult_26, %55 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "divf0"} : <f32>
    %76 = addf %53, %75 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf0"} : <f32>
    %77 = br %76 {handshake.bb = 3 : ui32, handshake.name = "br12"} : <f32>
    %78 = br %50 {handshake.bb = 3 : ui32, handshake.name = "br13"} : <i32>
    %79 = br %51 {handshake.bb = 3 : ui32, handshake.name = "br14"} : <i64>
    %80 = br %52 {handshake.bb = 3 : ui32, handshake.name = "br15"} : <i64>
    %81 = br %54 {handshake.bb = 3 : ui32, handshake.name = "br16"} : <i32>
    %82 = br %result_23 {handshake.bb = 3 : ui32, handshake.name = "br17"} : <>
    %83 = merge %trueResult {handshake.bb = 4 : ui32, handshake.name = "merge6"} : <i32>
    %84 = merge %trueResult_11 {handshake.bb = 4 : ui32, handshake.name = "merge7"} : <i64>
    %85 = merge %trueResult_13 {handshake.bb = 4 : ui32, handshake.name = "merge8"} : <i64>
    %86 = merge %trueResult_15 {handshake.bb = 4 : ui32, handshake.name = "merge9"} : <f32>
    %87 = merge %trueResult_17 {handshake.bb = 4 : ui32, handshake.name = "merge10"} : <i32>
    %88 = merge %trueResult_19 {handshake.bb = 4 : ui32, handshake.name = "merge11"} : <f32>
    %result_27, %index_28 = control_merge [%trueResult_21]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    %89 = source {handshake.bb = 4 : ui32, handshake.name = "source8"} : <>
    %90 = constant %89 {handshake.bb = 4 : ui32, handshake.name = "constant19", value = 4 : i64} : <>, <i64>
    %91 = source {handshake.bb = 4 : ui32, handshake.name = "source9"} : <>
    %92 = constant %91 {handshake.bb = 4 : ui32, handshake.name = "constant20", value = 3 : i64} : <>, <i64>
    %93 = source {handshake.bb = 4 : ui32, handshake.name = "source10"} : <>
    %94 = constant %93 {handshake.bb = 4 : ui32, handshake.name = "constant21", value = 2 : i64} : <>, <i64>
    %95 = source {handshake.bb = 4 : ui32, handshake.name = "source11"} : <>
    %96 = constant %95 {handshake.bb = 4 : ui32, handshake.name = "constant22", value = 1 : i64} : <>, <i64>
    %97 = extui %83 {handshake.bb = 4 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %98 = extui %87 {handshake.bb = 4 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %99 = shli %97, %96 {handshake.bb = 4 : ui32, handshake.name = "shli12"} : <i64>
    %100 = shli %97, %94 {handshake.bb = 4 : ui32, handshake.name = "shli13"} : <i64>
    %101 = addi %99, %100 {handshake.bb = 4 : ui32, handshake.name = "addi15"} : <i64>
    %102 = shli %97, %92 {handshake.bb = 4 : ui32, handshake.name = "shli14"} : <i64>
    %103 = shli %97, %90 {handshake.bb = 4 : ui32, handshake.name = "shli15"} : <i64>
    %104 = addi %102, %103 {handshake.bb = 4 : ui32, handshake.name = "addi16"} : <i64>
    %105 = addi %101, %104 {handshake.bb = 4 : ui32, handshake.name = "addi17"} : <i64>
    %106 = addi %105, %98 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i64>
    %107 = trunci %106 {handshake.bb = 4 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_29, %dataResult_30 = load[%107] %outputs_1#1 {handshake.bb = 4 : ui32, handshake.name = "load4"} : <i32>, <f32>, <i32>, <f32>
    %108 = mulf %dataResult_30, %88 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "mulf0"} : <f32>
    %109 = subf %86, %108 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "subf0"} : <f32>
    %110 = br %109 {handshake.bb = 4 : ui32, handshake.name = "br18"} : <f32>
    %111 = br %83 {handshake.bb = 4 : ui32, handshake.name = "br19"} : <i32>
    %112 = br %84 {handshake.bb = 4 : ui32, handshake.name = "br20"} : <i64>
    %113 = br %85 {handshake.bb = 4 : ui32, handshake.name = "br21"} : <i64>
    %114 = br %87 {handshake.bb = 4 : ui32, handshake.name = "br22"} : <i32>
    %115 = br %result_27 {handshake.bb = 4 : ui32, handshake.name = "br23"} : <>
    %116 = mux %index_32 [%77, %110] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<f32>, <f32>] to <f32>
    %117 = mux %index_32 [%78, %111] {handshake.bb = 5 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %118 = mux %index_32 [%79, %112] {handshake.bb = 5 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %119 = mux %index_32 [%80, %113] {handshake.bb = 5 : ui32, handshake.name = "mux9"} : <i1>, [<i64>, <i64>] to <i64>
    %120 = mux %index_32 [%81, %114] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %result_31, %index_32 = control_merge [%82, %115]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %121 = source {handshake.bb = 5 : ui32, handshake.name = "source12"} : <>
    %122 = constant %121 {handshake.bb = 5 : ui32, handshake.name = "constant23", value = 30 : i32} : <>, <i32>
    %123 = source {handshake.bb = 5 : ui32, handshake.name = "source13"} : <>
    %124 = constant %123 {handshake.bb = 5 : ui32, handshake.name = "constant24", value = 1 : i32} : <>, <i32>
    %125 = addi %120, %124 {handshake.bb = 5 : ui32, handshake.name = "addi4"} : <i32>
    %126 = cmpi ult, %125, %122 {handshake.bb = 5 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult_33, %falseResult_34 = cond_br %126, %116 {handshake.bb = 5 : ui32, handshake.name = "cond_br10"} : <i1>, <f32>
    %trueResult_35, %falseResult_36 = cond_br %126, %125 {handshake.bb = 5 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_37, %falseResult_38 = cond_br %126, %117 {handshake.bb = 5 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_39, %falseResult_40 = cond_br %126, %118 {handshake.bb = 5 : ui32, handshake.name = "cond_br13"} : <i1>, <i64>
    %trueResult_41, %falseResult_42 = cond_br %126, %119 {handshake.bb = 5 : ui32, handshake.name = "cond_br14"} : <i1>, <i64>
    %trueResult_43, %falseResult_44 = cond_br %126, %result_31 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %127 = constant %result_45 {handshake.bb = 6 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %128 = merge %falseResult_34 {handshake.bb = 6 : ui32, handshake.name = "merge12"} : <f32>
    %129 = merge %falseResult_38 {handshake.bb = 6 : ui32, handshake.name = "merge13"} : <i32>
    %result_45, %index_46 = control_merge [%falseResult_44]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    %130 = source {handshake.bb = 6 : ui32, handshake.name = "source14"} : <>
    %131 = constant %130 {handshake.bb = 6 : ui32, handshake.name = "constant25", value = 30 : i32} : <>, <i32>
    %132 = source {handshake.bb = 6 : ui32, handshake.name = "source15"} : <>
    %133 = constant %132 {handshake.bb = 6 : ui32, handshake.name = "constant26", value = 1 : i32} : <>, <i32>
    %134 = extui %129 {handshake.bb = 6 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %135 = trunci %134 {handshake.bb = 6 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_47, %dataResult_48 = store[%135] %128 {handshake.bb = 6 : ui32, handshake.name = "store5"} : <i32>, <f32>, <i32>, <f32>
    %136 = addi %129, %133 {handshake.bb = 6 : ui32, handshake.name = "addi5"} : <i32>
    %137 = cmpi ult, %136, %131 {handshake.bb = 6 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_49, %falseResult_50 = cond_br %137, %136 {handshake.bb = 6 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_51, %falseResult_52 = cond_br %137, %result_45 {handshake.bb = 6 : ui32, handshake.name = "cond_br17"} : <i1>, <>
    %result_53, %index_54 = control_merge [%falseResult_52]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    end {handshake.bb = 7 : ui32, handshake.name = "end0"} %memEnd_4, %memEnd_2, %memEnd_0, %memEnd, %arg8 : <>, <>, <>, <>, <>
  }
}

