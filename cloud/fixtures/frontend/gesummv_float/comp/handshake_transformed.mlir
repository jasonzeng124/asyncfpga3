module {
  handshake.func @gesummv_float(%arg0: !handshake.channel<f32>, %arg1: !handshake.channel<f32>, %arg2: memref<900xf32>, %arg3: memref<900xf32>, %arg4: memref<30xf32>, %arg5: memref<30xf32>, %arg6: memref<30xf32>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, %arg11: !handshake.control<>, %arg12: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["alpha", "beta", "A", "B", "tmp", "y", "x", "A_start", "B_start", "tmp_start", "y_start", "x_start", "start"], resNames = ["A_end", "B_end", "tmp_end", "y_end", "x_end", "end"]} {
    %0:3 = fork [3] %arg12 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg6 : memref<30xf32>] %arg11 (%addressResult_8) %119#4 {connectedBlocks = [2 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i5>) -> !handshake.channel<f32>
    %memEnd_0 = mem_controller[%arg5 : memref<30xf32>] %arg10 (%106, %addressResult_32, %dataResult_33) %119#3 {connectedBlocks = [3 : i32], handshake.name = "mem_controller6"} :    (!handshake.channel<i32>, !handshake.channel<i5>, !handshake.channel<f32>) -> ()
    %memEnd_1 = mem_controller[%arg4 : memref<30xf32>] %arg9 (%107, %addressResult_30, %dataResult_31) %119#2 {connectedBlocks = [3 : i32], handshake.name = "mem_controller7"} :    (!handshake.channel<i32>, !handshake.channel<i5>, !handshake.channel<f32>) -> ()
    %outputs_2, %memEnd_3 = mem_controller[%arg3 : memref<900xf32>] %arg8 (%addressResult) %119#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller8"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %outputs_4, %memEnd_5 = mem_controller[%arg2 : memref<900xf32>] %arg7 (%addressResult_10) %119#0 {connectedBlocks = [2 : i32], handshake.name = "mem_controller9"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui7"} : <i1> to <i5>
    %4 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <f32>
    %5 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <f32>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <>
    %7 = mux %11#0 [%3, %trueResult_34] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %8:3 = fork [3] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %9 = mux %11#1 [%4, %trueResult_36] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %10 = mux %11#2 [%5, %trueResult_38] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%6, %trueResult_40]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %12:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <>
    %13 = constant %12#2 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 0.000000e+00 : f32} : <>, <f32>
    %14 = br %13 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <f32>
    %15:2 = fork [2] %14 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <f32>
    %16 = constant %12#0 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = false} : <>, <i1>
    %17 = br %16 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i1>
    %18 = extui %17 {handshake.bb = 2 : ui32, handshake.name = "extui8"} : <i1> to <i5>
    %19 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <f32>
    %20 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <f32>
    %21 = br %8#2 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <i5>
    %22 = br %8#0 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <i5>
    %23 = br %8#1 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i5>
    %24 = br %12#1 {handshake.bb = 1 : ui32, handshake.name = "br13"} : <>
    %25 = mux %44#4 [%15#1, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<f32>, <f32>] to <f32>
    %26 = mux %44#5 [%15#0, %trueResult_12] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %27 = mux %44#3 [%18, %trueResult_14] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i5>, <i5>] to <i5>
    %28:4 = fork [4] %27 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i5>
    %29 = extui %28#0 {handshake.bb = 2 : ui32, handshake.name = "extui9"} : <i5> to <i10>
    %30 = extui %28#1 {handshake.bb = 2 : ui32, handshake.name = "extui10"} : <i5> to <i10>
    %31 = extui %28#3 {handshake.bb = 2 : ui32, handshake.name = "extui11"} : <i5> to <i6>
    %32 = constant %46 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 1 : i6} : <>, <i6>
    %33 = mux %44#6 [%19, %trueResult_16] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<f32>, <f32>] to <f32>
    %34 = mux %44#7 [%20, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<f32>, <f32>] to <f32>
    %35 = mux %44#2 [%21, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i5>, <i5>] to <i5>
    %36 = mux %44#0 [%22, %trueResult_22] {handshake.bb = 2 : ui32, handshake.name = "mux9"} : <i1>, [<i5>, <i5>] to <i5>
    %37:2 = fork [2] %36 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i5>
    %38 = extui %37#1 {handshake.bb = 2 : ui32, handshake.name = "extui12"} : <i5> to <i64>
    %39:4 = fork [4] %38 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i64>
    %40 = mux %44#1 [%23, %trueResult_24] {handshake.bb = 2 : ui32, handshake.name = "mux10"} : <i1>, [<i5>, <i5>] to <i5>
    %41:2 = fork [2] %40 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i5>
    %42 = extui %41#1 {handshake.bb = 2 : ui32, handshake.name = "extui13"} : <i5> to <i64>
    %43:4 = fork [4] %42 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i64>
    %result_6, %index_7 = control_merge [%24, %trueResult_26]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %44:8 = fork [8] %index_7 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i1>
    %45 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %46 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %47 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %48 = constant %47 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 4 : i64} : <>, <i64>
    %49:2 = fork [2] %48 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i64>
    %50 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %51 = constant %50 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 3 : i64} : <>, <i64>
    %52:2 = fork [2] %51 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i64>
    %53 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %54 = constant %53 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = 2 : i64} : <>, <i64>
    %55:2 = fork [2] %54 {handshake.bb = 2 : ui32, handshake.name = "fork13"} : <i64>
    %56 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %57 = constant %56 {handshake.bb = 2 : ui32, handshake.name = "constant16", value = 1 : i64} : <>, <i64>
    %58:2 = fork [2] %57 {handshake.bb = 2 : ui32, handshake.name = "fork14"} : <i64>
    %59 = shli %39#0, %58#1 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %60 = trunci %59 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i64> to <i10>
    %61 = shli %39#1, %55#1 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %62 = trunci %61 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i10>
    %63 = addi %60, %62 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i10>
    %64 = shli %39#2, %52#1 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %65 = trunci %64 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i64> to <i10>
    %66 = shli %39#3, %49#1 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %67 = trunci %66 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i64> to <i10>
    %68 = addi %65, %67 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i10>
    %69 = addi %63, %68 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i10>
    %70 = addi %69, %29 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i10>
    %addressResult, %dataResult = load[%70] %outputs_2 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <f32>, <i10>, <f32>
    %addressResult_8, %dataResult_9 = load[%28#2] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i5>, <f32>, <i5>, <f32>
    %71:2 = fork [2] %dataResult_9 {handshake.bb = 2 : ui32, handshake.name = "fork15"} : <f32>
    %72 = mulf %dataResult, %71#0 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %73 = addf %72, %25 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf0"} : <f32>
    %74 = shli %43#0, %58#0 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i64>
    %75 = trunci %74 {handshake.bb = 2 : ui32, handshake.name = "trunci4"} : <i64> to <i10>
    %76 = shli %43#1, %55#0 {handshake.bb = 2 : ui32, handshake.name = "shli5"} : <i64>
    %77 = trunci %76 {handshake.bb = 2 : ui32, handshake.name = "trunci5"} : <i64> to <i10>
    %78 = addi %75, %77 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i10>
    %79 = shli %43#2, %52#0 {handshake.bb = 2 : ui32, handshake.name = "shli6"} : <i64>
    %80 = trunci %79 {handshake.bb = 2 : ui32, handshake.name = "trunci6"} : <i64> to <i10>
    %81 = shli %43#3, %49#0 {handshake.bb = 2 : ui32, handshake.name = "shli7"} : <i64>
    %82 = trunci %81 {handshake.bb = 2 : ui32, handshake.name = "trunci7"} : <i64> to <i10>
    %83 = addi %80, %82 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i10>
    %84 = addi %78, %83 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i10>
    %85 = addi %84, %30 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i10>
    %addressResult_10, %dataResult_11 = load[%85] %outputs_4 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i10>, <f32>, <i10>, <f32>
    %86 = mulf %dataResult_11, %71#1 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf1"} : <f32>
    %87 = addf %86, %26 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf1"} : <f32>
    %88 = addi %31, %32 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i6>
    %89:2 = fork [2] %88 {handshake.bb = 2 : ui32, handshake.name = "fork16"} : <i6>
    %90 = trunci %89#0 {handshake.bb = 2 : ui32, handshake.name = "trunci8"} : <i6> to <i5>
    %91 = constant %45 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 30 : i6} : <>, <i6>
    %92 = cmpi ult, %89#1, %91 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i6>
    %93:9 = fork [9] %92 {handshake.bb = 2 : ui32, handshake.name = "fork17"} : <i1>
    %trueResult, %falseResult = cond_br %93#4, %73 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <f32>
    %trueResult_12, %falseResult_13 = cond_br %93#5, %87 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <f32>
    %trueResult_14, %falseResult_15 = cond_br %93#0, %90 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i5>
    sink %falseResult_15 {handshake.name = "sink0"} : <i5>
    %trueResult_16, %falseResult_17 = cond_br %93#6, %33 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <f32>
    %trueResult_18, %falseResult_19 = cond_br %93#7, %34 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %trueResult_20, %falseResult_21 = cond_br %93#3, %35 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i5>
    %trueResult_22, %falseResult_23 = cond_br %93#1, %37#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i5>
    sink %falseResult_23 {handshake.name = "sink1"} : <i5>
    %trueResult_24, %falseResult_25 = cond_br %93#2, %41#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i5>
    sink %falseResult_25 {handshake.name = "sink2"} : <i5>
    %trueResult_26, %falseResult_27 = cond_br %93#8, %result_6 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %94 = merge %falseResult_13 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <f32>
    %95:2 = fork [2] %94 {handshake.bb = 3 : ui32, handshake.name = "fork18"} : <f32>
    %96 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <f32>
    %97 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <f32>
    %98:2 = fork [2] %97 {handshake.bb = 3 : ui32, handshake.name = "fork19"} : <f32>
    %99 = merge %falseResult_19 {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <f32>
    %100:2 = fork [2] %99 {handshake.bb = 3 : ui32, handshake.name = "fork20"} : <f32>
    %101 = merge %falseResult_21 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i5>
    %102:3 = fork [3] %101 {handshake.bb = 3 : ui32, handshake.name = "fork21"} : <i5>
    %103 = extui %102#2 {handshake.bb = 3 : ui32, handshake.name = "extui14"} : <i5> to <i6>
    %104 = constant %109 {handshake.bb = 3 : ui32, handshake.name = "constant19", value = 1 : i6} : <>, <i6>
    %result_28, %index_29 = control_merge [%falseResult_27]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_29 {handshake.name = "sink3"} : <i1>
    %105:3 = fork [3] %result_28 {handshake.bb = 3 : ui32, handshake.name = "fork22"} : <>
    %106 = constant %105#0 {handshake.bb = 3 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %107 = constant %105#1 {handshake.bb = 3 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %108 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %109 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %addressResult_30, %dataResult_31 = store[%102#1] %95#0 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store3"} : <i5>, <f32>, <i5>, <f32>
    %110 = mulf %95#1, %98#1 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf2"} : <f32>
    %111 = mulf %96, %100#1 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf3"} : <f32>
    %112 = addf %110, %111 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf2"} : <f32>
    %addressResult_32, %dataResult_33 = store[%102#0] %112 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store4"} : <i5>, <f32>, <i5>, <f32>
    %113 = addi %103, %104 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i6>
    %114:2 = fork [2] %113 {handshake.bb = 3 : ui32, handshake.name = "fork23"} : <i6>
    %115 = trunci %114#0 {handshake.bb = 3 : ui32, handshake.name = "trunci9"} : <i6> to <i5>
    %116 = constant %108 {handshake.bb = 3 : ui32, handshake.name = "constant20", value = 30 : i6} : <>, <i6>
    %117 = cmpi ult, %114#1, %116 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i6>
    %118:4 = fork [4] %117 {handshake.bb = 3 : ui32, handshake.name = "fork24"} : <i1>
    %trueResult_34, %falseResult_35 = cond_br %118#0, %115 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <i5>
    sink %falseResult_35 {handshake.name = "sink4"} : <i5>
    %trueResult_36, %falseResult_37 = cond_br %118#1, %98#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <f32>
    sink %falseResult_37 {handshake.name = "sink5"} : <f32>
    %trueResult_38, %falseResult_39 = cond_br %118#2, %100#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <f32>
    sink %falseResult_39 {handshake.name = "sink6"} : <f32>
    %trueResult_40, %falseResult_41 = cond_br %118#3, %105#2 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %result_42, %index_43 = control_merge [%falseResult_41]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_43 {handshake.name = "sink7"} : <i1>
    %119:5 = fork [5] %result_42 {handshake.bb = 4 : ui32, handshake.name = "fork25"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd_5, %memEnd_3, %memEnd_1, %memEnd_0, %memEnd, %0#1 : <>, <>, <>, <>, <>, <>
  }
}

