module {
  handshake.func @gesummv_float(%arg0: !handshake.channel<f32>, %arg1: !handshake.channel<f32>, %arg2: memref<900xf32>, %arg3: memref<900xf32>, %arg4: memref<30xf32>, %arg5: memref<30xf32>, %arg6: memref<30xf32>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, %arg11: !handshake.control<>, %arg12: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["alpha", "beta", "A", "B", "tmp", "y", "x", "A_start", "B_start", "tmp_start", "y_start", "x_start", "start"], resNames = ["A_end", "B_end", "tmp_end", "y_end", "x_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg6 : memref<30xf32>] %arg11 (%addressResult_8) %result_42 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %memEnd_0 = mem_controller[%arg5 : memref<30xf32>] %arg10 (%68, %addressResult_32, %dataResult_33) %result_42 {connectedBlocks = [3 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>) -> ()
    %memEnd_1 = mem_controller[%arg4 : memref<30xf32>] %arg9 (%69, %addressResult_30, %dataResult_31) %result_42 {connectedBlocks = [3 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>) -> ()
    %outputs_2, %memEnd_3 = mem_controller[%arg3 : memref<900xf32>] %arg8 (%addressResult) %result_42 {connectedBlocks = [2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %outputs_4, %memEnd_5 = mem_controller[%arg2 : memref<900xf32>] %arg7 (%addressResult_10) %result_42 {connectedBlocks = [2 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %0 = constant %arg12 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %2 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <f32>
    %3 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <f32>
    %4 = br %arg12 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <>
    %5 = mux %index [%1, %trueResult_34] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%2, %trueResult_36] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %7 = mux %index [%3, %trueResult_38] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%4, %trueResult_40]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 0.000000e+00 : f32} : <>, <f32>
    %9 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 0 : i32} : <>, <i32>
    %10 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %11 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %12 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <f32>
    %13 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i32>
    %14 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <f32>
    %15 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <f32>
    %16 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <i32>
    %17 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <i64>
    %18 = br %11 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i64>
    %19 = br %result {handshake.bb = 1 : ui32, handshake.name = "br13"} : <>
    %20 = mux %index_7 [%12, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<f32>, <f32>] to <f32>
    %21 = mux %index_7 [%12, %trueResult_12] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %22 = mux %index_7 [%13, %trueResult_14] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %23 = mux %index_7 [%14, %trueResult_16] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<f32>, <f32>] to <f32>
    %24 = mux %index_7 [%15, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<f32>, <f32>] to <f32>
    %25 = mux %index_7 [%16, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %26 = mux %index_7 [%17, %trueResult_22] {handshake.bb = 2 : ui32, handshake.name = "mux9"} : <i1>, [<i64>, <i64>] to <i64>
    %27 = mux %index_7 [%18, %trueResult_24] {handshake.bb = 2 : ui32, handshake.name = "mux10"} : <i1>, [<i64>, <i64>] to <i64>
    %result_6, %index_7 = control_merge [%19, %trueResult_26]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %28 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %29 = constant %28 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 30 : i32} : <>, <i32>
    %30 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %31 = constant %30 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 1 : i32} : <>, <i32>
    %32 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %33 = constant %32 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 4 : i64} : <>, <i64>
    %34 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %35 = constant %34 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 3 : i64} : <>, <i64>
    %36 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %37 = constant %36 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = 2 : i64} : <>, <i64>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %39 = constant %38 {handshake.bb = 2 : ui32, handshake.name = "constant16", value = 1 : i64} : <>, <i64>
    %40 = extui %22 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %41 = shli %26, %39 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %42 = shli %26, %37 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %43 = addi %41, %42 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i64>
    %44 = shli %26, %35 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %45 = shli %26, %33 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %46 = addi %44, %45 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i64>
    %47 = addi %43, %46 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i64>
    %48 = addi %47, %40 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %49 = trunci %48 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%49] %outputs_2 {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %50 = extui %22 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %51 = trunci %50 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_8, %dataResult_9 = load[%51] %outputs {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <f32>, <i32>, <f32>
    %52 = mulf %dataResult, %dataResult_9 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %53 = addf %52, %20 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf0"} : <f32>
    %54 = extui %22 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %55 = shli %27, %39 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i64>
    %56 = shli %27, %37 {handshake.bb = 2 : ui32, handshake.name = "shli5"} : <i64>
    %57 = addi %55, %56 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i64>
    %58 = shli %27, %35 {handshake.bb = 2 : ui32, handshake.name = "shli6"} : <i64>
    %59 = shli %27, %33 {handshake.bb = 2 : ui32, handshake.name = "shli7"} : <i64>
    %60 = addi %58, %59 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i64>
    %61 = addi %57, %60 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i64>
    %62 = addi %61, %54 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i64>
    %63 = trunci %62 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_10, %dataResult_11 = load[%63] %outputs_4 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <f32>, <i32>, <f32>
    %64 = mulf %dataResult_11, %dataResult_9 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf1"} : <f32>
    %65 = addf %64, %21 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf1"} : <f32>
    %66 = addi %22, %31 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %67 = cmpi ult, %66, %29 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %67, %53 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <f32>
    %trueResult_12, %falseResult_13 = cond_br %67, %65 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <f32>
    %trueResult_14, %falseResult_15 = cond_br %67, %66 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %67, %23 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <f32>
    %trueResult_18, %falseResult_19 = cond_br %67, %24 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %trueResult_20, %falseResult_21 = cond_br %67, %25 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %67, %26 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i64>
    %trueResult_24, %falseResult_25 = cond_br %67, %27 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i64>
    %trueResult_26, %falseResult_27 = cond_br %67, %result_6 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %68 = constant %result_28 {handshake.bb = 3 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %69 = constant %result_28 {handshake.bb = 3 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %70 = merge %falseResult_13 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <f32>
    %71 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <f32>
    %72 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <f32>
    %73 = merge %falseResult_19 {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <f32>
    %74 = merge %falseResult_21 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i32>
    %result_28, %index_29 = control_merge [%falseResult_27]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %75 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %76 = constant %75 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 30 : i32} : <>, <i32>
    %77 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %78 = constant %77 {handshake.bb = 3 : ui32, handshake.name = "constant18", value = 1 : i32} : <>, <i32>
    %79 = extui %74 {handshake.bb = 3 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %80 = trunci %79 {handshake.bb = 3 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_30, %dataResult_31 = store[%80] %70 {handshake.bb = 3 : ui32, handshake.name = "store3"} : <i32>, <f32>, <i32>, <f32>
    %81 = mulf %70, %72 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf2"} : <f32>
    %82 = mulf %71, %73 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf3"} : <f32>
    %83 = addf %81, %82 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf2"} : <f32>
    %84 = extui %74 {handshake.bb = 3 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %85 = trunci %84 {handshake.bb = 3 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_32, %dataResult_33 = store[%85] %83 {handshake.bb = 3 : ui32, handshake.name = "store4"} : <i32>, <f32>, <i32>, <f32>
    %86 = addi %74, %78 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %87 = cmpi ult, %86, %76 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_34, %falseResult_35 = cond_br %87, %86 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_36, %falseResult_37 = cond_br %87, %72 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <f32>
    %trueResult_38, %falseResult_39 = cond_br %87, %73 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <f32>
    %trueResult_40, %falseResult_41 = cond_br %87, %result_28 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %result_42, %index_43 = control_merge [%falseResult_41]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd_5, %memEnd_3, %memEnd_1, %memEnd_0, %memEnd, %arg12 : <>, <>, <>, <>, <>, <>
  }
}

