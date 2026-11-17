module {
  handshake.func @gemm_float(%arg0: !handshake.channel<f32>, %arg1: !handshake.channel<f32>, %arg2: memref<900xf32>, %arg3: memref<900xf32>, %arg4: memref<900xf32>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["alpha", "beta", "A", "B", "C", "A_start", "B_start", "C_start", "start"], resNames = ["A_end", "B_end", "C_end", "end"]} {
    %0:3 = fork [3] %arg8 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg4 : memref<900xf32>] %arg7 (%addressResult, %158, %addressResult_34, %dataResult_35) %200#2 {connectedBlocks = [2 : i32, 4 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i10>, !handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<f32>) -> !handshake.channel<f32>
    %outputs_0, %memEnd_1 = mem_controller[%arg3 : memref<900xf32>] %arg6 (%addressResult_10) %200#1 {connectedBlocks = [3 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %outputs_2, %memEnd_3 = mem_controller[%arg2 : memref<900xf32>] %arg5 (%addressResult_8) %200#0 {connectedBlocks = [3 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui8"} : <i1> to <i5>
    %4 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <f32>
    %5 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <f32>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %7 = mux %11#0 [%3, %trueResult_54] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %8:4 = fork [4] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %9 = mux %11#1 [%4, %trueResult_56] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %10 = mux %11#2 [%5, %trueResult_58] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%6, %trueResult_60]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %12:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <>
    %13 = constant %12#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %14 = br %13 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i1>
    %15 = extui %14 {handshake.bb = 2 : ui32, handshake.name = "extui9"} : <i1> to <i5>
    %16 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <f32>
    %17 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <f32>
    %18 = br %8#3 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <i5>
    %19 = br %8#0 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <i5>
    %20 = br %8#1 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i5>
    %21 = br %8#2 {handshake.bb = 1 : ui32, handshake.name = "br13"} : <i5>
    %22 = br %12#1 {handshake.bb = 1 : ui32, handshake.name = "br14"} : <>
    %23 = mux %36#4 [%15, %trueResult_36] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i5>, <i5>] to <i5>
    %24:3 = fork [3] %23 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i5>
    %25 = extui %24#0 {handshake.bb = 2 : ui32, handshake.name = "extui10"} : <i5> to <i10>
    %26 = mux %36#5 [%16, %trueResult_38] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %27 = mux %36#6 [%17, %trueResult_40] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<f32>, <f32>] to <f32>
    %28:2 = fork [2] %27 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <f32>
    %29 = mux %36#3 [%18, %trueResult_42] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i5>, <i5>] to <i5>
    %30 = mux %36#0 [%19, %trueResult_44] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i5>, <i5>] to <i5>
    %31:2 = fork [2] %30 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i5>
    %32 = extui %31#1 {handshake.bb = 2 : ui32, handshake.name = "extui11"} : <i5> to <i64>
    %33:4 = fork [4] %32 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i64>
    %34 = mux %36#1 [%20, %trueResult_46] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i5>, <i5>] to <i5>
    %35 = mux %36#2 [%21, %trueResult_48] {handshake.bb = 2 : ui32, handshake.name = "mux9"} : <i1>, [<i5>, <i5>] to <i5>
    %result_4, %index_5 = control_merge [%22, %trueResult_50]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %36:7 = fork [7] %index_5 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %37:2 = fork [2] %result_4 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %39 = constant %38 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 4 : i64} : <>, <i64>
    %40 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %41 = constant %40 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 3 : i64} : <>, <i64>
    %42 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %43 = constant %42 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 2 : i64} : <>, <i64>
    %44 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %45 = constant %44 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 1 : i64} : <>, <i64>
    %46 = shli %33#0, %45 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %47 = trunci %46 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i64> to <i10>
    %48 = shli %33#1, %43 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %49 = trunci %48 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i10>
    %50 = addi %47, %49 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i10>
    %51 = shli %33#2, %41 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %52 = trunci %51 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i64> to <i10>
    %53 = shli %33#3, %39 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %54 = trunci %53 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i64> to <i10>
    %55 = addi %52, %54 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i10>
    %56 = addi %50, %55 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i10>
    %57 = addi %56, %25 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i10>
    %addressResult, %dataResult = load[%57] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <f32>, <i10>, <f32>
    %58 = mulf %dataResult, %28#1 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %59 = br %58 {handshake.bb = 2 : ui32, handshake.name = "br15"} : <f32>
    %60 = constant %37#0 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %61 = br %60 {handshake.bb = 2 : ui32, handshake.name = "br16"} : <i1>
    %62 = extui %61 {handshake.bb = 3 : ui32, handshake.name = "extui12"} : <i1> to <i5>
    %63 = br %26 {handshake.bb = 2 : ui32, handshake.name = "br17"} : <f32>
    %64 = br %28#0 {handshake.bb = 2 : ui32, handshake.name = "br18"} : <f32>
    %65 = br %29 {handshake.bb = 2 : ui32, handshake.name = "br19"} : <i5>
    %66 = br %31#0 {handshake.bb = 2 : ui32, handshake.name = "br20"} : <i5>
    %67 = br %34 {handshake.bb = 2 : ui32, handshake.name = "br21"} : <i5>
    %68 = br %35 {handshake.bb = 2 : ui32, handshake.name = "br22"} : <i5>
    %69 = br %24#2 {handshake.bb = 2 : ui32, handshake.name = "br23"} : <i5>
    %70 = br %24#1 {handshake.bb = 2 : ui32, handshake.name = "br24"} : <i5>
    %71 = br %37#1 {handshake.bb = 2 : ui32, handshake.name = "br25"} : <>
    %72 = mux %92#7 [%59, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<f32>, <f32>] to <f32>
    %73 = mux %92#6 [%62, %trueResult_12] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i5>, <i5>] to <i5>
    %74:3 = fork [3] %73 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i5>
    %75 = extui %74#0 {handshake.bb = 3 : ui32, handshake.name = "extui13"} : <i5> to <i10>
    %76 = extui %74#1 {handshake.bb = 3 : ui32, handshake.name = "extui14"} : <i5> to <i6>
    %77 = constant %94 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 1 : i6} : <>, <i6>
    %78 = mux %92#8 [%63, %trueResult_14] {handshake.bb = 3 : ui32, handshake.name = "mux12"} : <i1>, [<f32>, <f32>] to <f32>
    %79:2 = fork [2] %78 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <f32>
    %80 = mux %92#9 [%64, %trueResult_16] {handshake.bb = 3 : ui32, handshake.name = "mux13"} : <i1>, [<f32>, <f32>] to <f32>
    %81 = mux %92#3 [%65, %trueResult_18] {handshake.bb = 3 : ui32, handshake.name = "mux14"} : <i1>, [<i5>, <i5>] to <i5>
    %82 = mux %92#0 [%66, %trueResult_20] {handshake.bb = 3 : ui32, handshake.name = "mux15"} : <i1>, [<i5>, <i5>] to <i5>
    %83 = mux %92#1 [%67, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux16"} : <i1>, [<i5>, <i5>] to <i5>
    %84:2 = fork [2] %83 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i5>
    %85 = extui %84#1 {handshake.bb = 3 : ui32, handshake.name = "extui15"} : <i5> to <i64>
    %86:4 = fork [4] %85 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i64>
    %87 = mux %92#2 [%68, %trueResult_24] {handshake.bb = 3 : ui32, handshake.name = "mux17"} : <i1>, [<i5>, <i5>] to <i5>
    %88 = mux %92#5 [%69, %trueResult_26] {handshake.bb = 3 : ui32, handshake.name = "mux18"} : <i1>, [<i5>, <i5>] to <i5>
    %89 = mux %92#4 [%70, %trueResult_28] {handshake.bb = 3 : ui32, handshake.name = "mux19"} : <i1>, [<i5>, <i5>] to <i5>
    %90:2 = fork [2] %89 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i5>
    %91 = extui %90#0 {handshake.bb = 3 : ui32, handshake.name = "extui16"} : <i5> to <i10>
    %result_6, %index_7 = control_merge [%71, %trueResult_30]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %92:10 = fork [10] %index_7 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i1>
    %93 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %94 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %95 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %96 = constant %95 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 4 : i64} : <>, <i64>
    %97:2 = fork [2] %96 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i64>
    %98 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %99 = constant %98 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 3 : i64} : <>, <i64>
    %100:2 = fork [2] %99 {handshake.bb = 3 : ui32, handshake.name = "fork17"} : <i64>
    %101 = source {handshake.bb = 3 : ui32, handshake.name = "source8"} : <>
    %102 = constant %101 {handshake.bb = 3 : ui32, handshake.name = "constant18", value = 2 : i64} : <>, <i64>
    %103:2 = fork [2] %102 {handshake.bb = 3 : ui32, handshake.name = "fork18"} : <i64>
    %104 = source {handshake.bb = 3 : ui32, handshake.name = "source9"} : <>
    %105 = constant %104 {handshake.bb = 3 : ui32, handshake.name = "constant19", value = 1 : i64} : <>, <i64>
    %106:2 = fork [2] %105 {handshake.bb = 3 : ui32, handshake.name = "fork19"} : <i64>
    %107 = shli %86#0, %106#1 {handshake.bb = 3 : ui32, handshake.name = "shli4"} : <i64>
    %108 = trunci %107 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i64> to <i10>
    %109 = shli %86#1, %103#1 {handshake.bb = 3 : ui32, handshake.name = "shli5"} : <i64>
    %110 = trunci %109 {handshake.bb = 3 : ui32, handshake.name = "trunci5"} : <i64> to <i10>
    %111 = addi %108, %110 {handshake.bb = 3 : ui32, handshake.name = "addi10"} : <i10>
    %112 = shli %86#2, %100#1 {handshake.bb = 3 : ui32, handshake.name = "shli6"} : <i64>
    %113 = trunci %112 {handshake.bb = 3 : ui32, handshake.name = "trunci6"} : <i64> to <i10>
    %114 = shli %86#3, %97#1 {handshake.bb = 3 : ui32, handshake.name = "shli7"} : <i64>
    %115 = trunci %114 {handshake.bb = 3 : ui32, handshake.name = "trunci7"} : <i64> to <i10>
    %116 = addi %113, %115 {handshake.bb = 3 : ui32, handshake.name = "addi11"} : <i10>
    %117 = addi %111, %116 {handshake.bb = 3 : ui32, handshake.name = "addi12"} : <i10>
    %118 = addi %117, %75 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i10>
    %addressResult_8, %dataResult_9 = load[%118] %outputs_2 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <f32>, <i10>, <f32>
    %119 = mulf %dataResult_9, %79#1 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf1"} : <f32>
    %120 = extui %74#2 {handshake.bb = 3 : ui32, handshake.name = "extui6"} : <i5> to <i64>
    %121:4 = fork [4] %120 {handshake.bb = 3 : ui32, handshake.name = "fork20"} : <i64>
    %122 = shli %121#3, %106#0 {handshake.bb = 3 : ui32, handshake.name = "shli8"} : <i64>
    %123 = trunci %122 {handshake.bb = 3 : ui32, handshake.name = "trunci8"} : <i64> to <i10>
    %124 = shli %121#2, %103#0 {handshake.bb = 3 : ui32, handshake.name = "shli9"} : <i64>
    %125 = trunci %124 {handshake.bb = 3 : ui32, handshake.name = "trunci9"} : <i64> to <i10>
    %126 = addi %123, %125 {handshake.bb = 3 : ui32, handshake.name = "addi13"} : <i10>
    %127 = shli %121#1, %100#0 {handshake.bb = 3 : ui32, handshake.name = "shli10"} : <i64>
    %128 = trunci %127 {handshake.bb = 3 : ui32, handshake.name = "trunci10"} : <i64> to <i10>
    %129 = shli %121#0, %97#0 {handshake.bb = 3 : ui32, handshake.name = "shli11"} : <i64>
    %130 = trunci %129 {handshake.bb = 3 : ui32, handshake.name = "trunci11"} : <i64> to <i10>
    %131 = addi %128, %130 {handshake.bb = 3 : ui32, handshake.name = "addi14"} : <i10>
    %132 = addi %126, %131 {handshake.bb = 3 : ui32, handshake.name = "addi15"} : <i10>
    %133 = addi %132, %91 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i10>
    %addressResult_10, %dataResult_11 = load[%133] %outputs_0 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i10>, <f32>, <i10>, <f32>
    %134 = mulf %119, %dataResult_11 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf2"} : <f32>
    %135 = addf %72, %134 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf0"} : <f32>
    %136 = addi %76, %77 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i6>
    %137:2 = fork [2] %136 {handshake.bb = 3 : ui32, handshake.name = "fork21"} : <i6>
    %138 = trunci %137#0 {handshake.bb = 3 : ui32, handshake.name = "trunci12"} : <i6> to <i5>
    %139 = constant %93 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = 20 : i6} : <>, <i6>
    %140 = cmpi ult, %137#1, %139 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i6>
    %141:11 = fork [11] %140 {handshake.bb = 3 : ui32, handshake.name = "fork22"} : <i1>
    %trueResult, %falseResult = cond_br %141#7, %135 {handshake.bb = 3 : ui32, handshake.name = "cond_br3"} : <i1>, <f32>
    %trueResult_12, %falseResult_13 = cond_br %141#0, %138 {handshake.bb = 3 : ui32, handshake.name = "cond_br4"} : <i1>, <i5>
    sink %falseResult_13 {handshake.name = "sink0"} : <i5>
    %trueResult_14, %falseResult_15 = cond_br %141#8, %79#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <f32>
    %trueResult_16, %falseResult_17 = cond_br %141#9, %80 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %trueResult_18, %falseResult_19 = cond_br %141#4, %81 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i5>
    %trueResult_20, %falseResult_21 = cond_br %141#1, %82 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i5>
    %trueResult_22, %falseResult_23 = cond_br %141#2, %84#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i5>
    %trueResult_24, %falseResult_25 = cond_br %141#3, %87 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <i5>
    %trueResult_26, %falseResult_27 = cond_br %141#6, %88 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <i5>
    %trueResult_28, %falseResult_29 = cond_br %141#5, %90#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i5>
    sink %falseResult_29 {handshake.name = "sink1"} : <i5>
    %trueResult_30, %falseResult_31 = cond_br %141#10, %result_6 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %142 = merge %falseResult {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <f32>
    %143 = merge %falseResult_15 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <f32>
    %144 = merge %falseResult_17 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <f32>
    %145 = merge %falseResult_19 {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <i5>
    %146 = merge %falseResult_21 {handshake.bb = 4 : ui32, handshake.name = "merge4"} : <i5>
    %147 = merge %falseResult_23 {handshake.bb = 4 : ui32, handshake.name = "merge5"} : <i5>
    %148 = merge %falseResult_25 {handshake.bb = 4 : ui32, handshake.name = "merge6"} : <i5>
    %149:2 = fork [2] %148 {handshake.bb = 4 : ui32, handshake.name = "fork23"} : <i5>
    %150 = extui %149#1 {handshake.bb = 4 : ui32, handshake.name = "extui17"} : <i5> to <i64>
    %151:4 = fork [4] %150 {handshake.bb = 4 : ui32, handshake.name = "fork24"} : <i64>
    %152 = merge %falseResult_27 {handshake.bb = 4 : ui32, handshake.name = "merge7"} : <i5>
    %153:2 = fork [2] %152 {handshake.bb = 4 : ui32, handshake.name = "fork25"} : <i5>
    %154 = extui %153#0 {handshake.bb = 4 : ui32, handshake.name = "extui18"} : <i5> to <i10>
    %155 = extui %153#1 {handshake.bb = 4 : ui32, handshake.name = "extui19"} : <i5> to <i6>
    %156 = constant %160 {handshake.bb = 4 : ui32, handshake.name = "constant28", value = 1 : i6} : <>, <i6>
    %result_32, %index_33 = control_merge [%falseResult_31]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_33 {handshake.name = "sink2"} : <i1>
    %157:2 = fork [2] %result_32 {handshake.bb = 4 : ui32, handshake.name = "fork26"} : <>
    %158 = constant %157#0 {handshake.bb = 4 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %159 = source {handshake.bb = 4 : ui32, handshake.name = "source10"} : <>
    %160 = source {handshake.bb = 4 : ui32, handshake.name = "source11"} : <>
    %161 = source {handshake.bb = 4 : ui32, handshake.name = "source12"} : <>
    %162 = constant %161 {handshake.bb = 4 : ui32, handshake.name = "constant22", value = 4 : i64} : <>, <i64>
    %163 = source {handshake.bb = 4 : ui32, handshake.name = "source13"} : <>
    %164 = constant %163 {handshake.bb = 4 : ui32, handshake.name = "constant23", value = 3 : i64} : <>, <i64>
    %165 = source {handshake.bb = 4 : ui32, handshake.name = "source14"} : <>
    %166 = constant %165 {handshake.bb = 4 : ui32, handshake.name = "constant24", value = 2 : i64} : <>, <i64>
    %167 = source {handshake.bb = 4 : ui32, handshake.name = "source15"} : <>
    %168 = constant %167 {handshake.bb = 4 : ui32, handshake.name = "constant25", value = 1 : i64} : <>, <i64>
    %169 = shli %151#0, %168 {handshake.bb = 4 : ui32, handshake.name = "shli12"} : <i64>
    %170 = trunci %169 {handshake.bb = 4 : ui32, handshake.name = "trunci13"} : <i64> to <i10>
    %171 = shli %151#1, %166 {handshake.bb = 4 : ui32, handshake.name = "shli13"} : <i64>
    %172 = trunci %171 {handshake.bb = 4 : ui32, handshake.name = "trunci14"} : <i64> to <i10>
    %173 = addi %170, %172 {handshake.bb = 4 : ui32, handshake.name = "addi16"} : <i10>
    %174 = shli %151#2, %164 {handshake.bb = 4 : ui32, handshake.name = "shli14"} : <i64>
    %175 = trunci %174 {handshake.bb = 4 : ui32, handshake.name = "trunci15"} : <i64> to <i10>
    %176 = shli %151#3, %162 {handshake.bb = 4 : ui32, handshake.name = "shli15"} : <i64>
    %177 = trunci %176 {handshake.bb = 4 : ui32, handshake.name = "trunci16"} : <i64> to <i10>
    %178 = addi %175, %177 {handshake.bb = 4 : ui32, handshake.name = "addi17"} : <i10>
    %179 = addi %173, %178 {handshake.bb = 4 : ui32, handshake.name = "addi18"} : <i10>
    %180 = addi %179, %154 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i10>
    %addressResult_34, %dataResult_35 = store[%180] %142 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store3"} : <i10>, <f32>, <i10>, <f32>
    %181 = addi %155, %156 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i6>
    %182:2 = fork [2] %181 {handshake.bb = 4 : ui32, handshake.name = "fork27"} : <i6>
    %183 = trunci %182#0 {handshake.bb = 4 : ui32, handshake.name = "trunci17"} : <i6> to <i5>
    %184 = constant %159 {handshake.bb = 4 : ui32, handshake.name = "constant29", value = 20 : i6} : <>, <i6>
    %185 = cmpi ult, %182#1, %184 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i6>
    %186:8 = fork [8] %185 {handshake.bb = 4 : ui32, handshake.name = "fork28"} : <i1>
    %trueResult_36, %falseResult_37 = cond_br %186#0, %183 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i5>
    sink %falseResult_37 {handshake.name = "sink3"} : <i5>
    %trueResult_38, %falseResult_39 = cond_br %186#5, %143 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <f32>
    %trueResult_40, %falseResult_41 = cond_br %186#6, %144 {handshake.bb = 4 : ui32, handshake.name = "cond_br16"} : <i1>, <f32>
    %trueResult_42, %falseResult_43 = cond_br %186#4, %145 {handshake.bb = 4 : ui32, handshake.name = "cond_br17"} : <i1>, <i5>
    %trueResult_44, %falseResult_45 = cond_br %186#1, %146 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <i5>
    sink %falseResult_45 {handshake.name = "sink4"} : <i5>
    %trueResult_46, %falseResult_47 = cond_br %186#2, %147 {handshake.bb = 4 : ui32, handshake.name = "cond_br19"} : <i1>, <i5>
    sink %falseResult_47 {handshake.name = "sink5"} : <i5>
    %trueResult_48, %falseResult_49 = cond_br %186#3, %149#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br20"} : <i1>, <i5>
    sink %falseResult_49 {handshake.name = "sink6"} : <i5>
    %trueResult_50, %falseResult_51 = cond_br %186#7, %157#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br21"} : <i1>, <>
    %187 = merge %falseResult_39 {handshake.bb = 5 : ui32, handshake.name = "merge8"} : <f32>
    %188 = merge %falseResult_41 {handshake.bb = 5 : ui32, handshake.name = "merge9"} : <f32>
    %189 = merge %falseResult_43 {handshake.bb = 5 : ui32, handshake.name = "merge10"} : <i5>
    %190 = extui %189 {handshake.bb = 5 : ui32, handshake.name = "extui20"} : <i5> to <i6>
    %191 = constant %193 {handshake.bb = 5 : ui32, handshake.name = "constant30", value = 1 : i6} : <>, <i6>
    %result_52, %index_53 = control_merge [%falseResult_51]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_53 {handshake.name = "sink7"} : <i1>
    %192 = source {handshake.bb = 5 : ui32, handshake.name = "source16"} : <>
    %193 = source {handshake.bb = 5 : ui32, handshake.name = "source17"} : <>
    %194 = addi %190, %191 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i6>
    %195:2 = fork [2] %194 {handshake.bb = 5 : ui32, handshake.name = "fork29"} : <i6>
    %196 = trunci %195#0 {handshake.bb = 5 : ui32, handshake.name = "trunci18"} : <i6> to <i5>
    %197 = constant %192 {handshake.bb = 5 : ui32, handshake.name = "constant31", value = 20 : i6} : <>, <i6>
    %198 = cmpi ult, %195#1, %197 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i6>
    %199:4 = fork [4] %198 {handshake.bb = 5 : ui32, handshake.name = "fork30"} : <i1>
    %trueResult_54, %falseResult_55 = cond_br %199#0, %196 {handshake.bb = 5 : ui32, handshake.name = "cond_br22"} : <i1>, <i5>
    sink %falseResult_55 {handshake.name = "sink8"} : <i5>
    %trueResult_56, %falseResult_57 = cond_br %199#1, %187 {handshake.bb = 5 : ui32, handshake.name = "cond_br23"} : <i1>, <f32>
    sink %falseResult_57 {handshake.name = "sink9"} : <f32>
    %trueResult_58, %falseResult_59 = cond_br %199#2, %188 {handshake.bb = 5 : ui32, handshake.name = "cond_br24"} : <i1>, <f32>
    sink %falseResult_59 {handshake.name = "sink10"} : <f32>
    %trueResult_60, %falseResult_61 = cond_br %199#3, %result_52 {handshake.bb = 5 : ui32, handshake.name = "cond_br25"} : <i1>, <>
    %result_62, %index_63 = control_merge [%falseResult_61]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_63 {handshake.name = "sink11"} : <i1>
    %200:3 = fork [3] %result_62 {handshake.bb = 6 : ui32, handshake.name = "fork31"} : <>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %memEnd_3, %memEnd_1, %memEnd, %0#1 : <>, <>, <>, <>
  }
}

