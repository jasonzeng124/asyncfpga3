module {
  handshake.func @gsumif(%arg0: memref<1000xf32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<1000xf32>] %arg1 (%addressResult) %result_30 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0.000000e+00 : f32} : <>, <f32>
    %2 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i32>
    %3 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <f32>
    %4 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %5 = mux %index [%2, %trueResult_24] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%3, %trueResult_26] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%4, %trueResult_28]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = 0.000000e+00 : f32} : <>, <f32>
    %9 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = trunci %9 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%10] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %11 = cmpf ult, %dataResult, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %trueResult, %falseResult = cond_br %11, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <f32>
    %trueResult_0, %falseResult_1 = cond_br %11, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %11, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %trueResult_4, %falseResult_5 = cond_br %11, %dataResult {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %12 = merge %falseResult_1 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %13 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <f32>
    %14 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <f32>
    %result_6, %index_7 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %15 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %16 = constant %15 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 5 : i32} : <>, <i32>
    %17 = cmpi ugt, %12, %16 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %17, %12 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %17, %13 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <f32>
    %trueResult_12, %falseResult_13 = cond_br %17, %14 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <f32>
    %trueResult_14, %falseResult_15 = cond_br %17, %result_6 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %18 = merge %trueResult_8 {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <i32>
    %19 = merge %trueResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <f32>
    %20 = merge %trueResult_12 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <f32>
    %result_16, %index_17 = control_merge [%trueResult_14]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %21 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %22 = constant %21 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 1.250000e-01 : f32} : <>, <f32>
    %23 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %24 = constant %23 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 5.000000e-01 : f32} : <>, <f32>
    %25 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %26 = constant %25 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 2.500000e-01 : f32} : <>, <f32>
    %27 = addf %20, %26 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf0"} : <f32>
    %28 = mulf %27, %20 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf0"} : <f32>
    %29 = addf %28, %24 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf1"} : <f32>
    %30 = mulf %29, %20 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf1"} : <f32>
    %31 = addf %30, %22 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf2"} : <f32>
    %32 = br %31 {handshake.bb = 3 : ui32, handshake.name = "br7"} : <f32>
    %33 = br %18 {handshake.bb = 3 : ui32, handshake.name = "br8"} : <i32>
    %34 = br %19 {handshake.bb = 3 : ui32, handshake.name = "br9"} : <f32>
    %35 = br %result_16 {handshake.bb = 3 : ui32, handshake.name = "br10"} : <>
    %36 = merge %falseResult_9 {handshake.bb = 4 : ui32, handshake.name = "merge6"} : <i32>
    %37 = merge %falseResult_11 {handshake.bb = 4 : ui32, handshake.name = "merge7"} : <f32>
    %38 = merge %falseResult_13 {handshake.bb = 4 : ui32, handshake.name = "merge8"} : <f32>
    %result_18, %index_19 = control_merge [%falseResult_15]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    %39 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %40 = constant %39 {handshake.bb = 4 : ui32, handshake.name = "constant16", value = 2.100000e-01 : f32} : <>, <f32>
    %41 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %42 = constant %41 {handshake.bb = 4 : ui32, handshake.name = "constant17", value = 0.699999988 : f32} : <>, <f32>
    %43 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %44 = constant %43 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 6.400000e-01 : f32} : <>, <f32>
    %45 = addf %38, %44 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "addf3"} : <f32>
    %46 = mulf %45, %38 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "mulf2"} : <f32>
    %47 = addf %46, %42 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "addf4"} : <f32>
    %48 = mulf %47, %38 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "mulf3"} : <f32>
    %49 = addf %48, %40 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "addf5"} : <f32>
    %50 = br %49 {handshake.bb = 4 : ui32, handshake.name = "br11"} : <f32>
    %51 = br %36 {handshake.bb = 4 : ui32, handshake.name = "br12"} : <i32>
    %52 = br %37 {handshake.bb = 4 : ui32, handshake.name = "br13"} : <f32>
    %53 = br %result_18 {handshake.bb = 4 : ui32, handshake.name = "br14"} : <>
    %54 = mux %index_21 [%32, %50] {handshake.bb = 5 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %55 = mux %index_21 [%33, %51] {handshake.bb = 5 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %56 = mux %index_21 [%34, %52] {handshake.bb = 5 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %result_20, %index_21 = control_merge [%35, %53]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %57 = addf %56, %54 {fastmath = #arith.fastmath<none>, handshake.bb = 5 : ui32, handshake.name = "addf6"} : <f32>
    %58 = br %57 {handshake.bb = 5 : ui32, handshake.name = "br15"} : <f32>
    %59 = br %55 {handshake.bb = 5 : ui32, handshake.name = "br16"} : <i32>
    %60 = br %result_20 {handshake.bb = 5 : ui32, handshake.name = "br17"} : <>
    %61 = mux %index_23 [%trueResult, %58] {handshake.bb = 6 : ui32, handshake.name = "mux5"} : <i1>, [<f32>, <f32>] to <f32>
    %62 = mux %index_23 [%trueResult_0, %59] {handshake.bb = 6 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %result_22, %index_23 = control_merge [%trueResult_2, %60]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %63 = source {handshake.bb = 6 : ui32, handshake.name = "source8"} : <>
    %64 = constant %63 {handshake.bb = 6 : ui32, handshake.name = "constant19", value = 1000 : i32} : <>, <i32>
    %65 = source {handshake.bb = 6 : ui32, handshake.name = "source9"} : <>
    %66 = constant %65 {handshake.bb = 6 : ui32, handshake.name = "constant20", value = 1 : i32} : <>, <i32>
    %67 = addi %62, %66 {handshake.bb = 6 : ui32, handshake.name = "addi0"} : <i32>
    %68 = cmpi ult, %67, %64 {handshake.bb = 6 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_24, %falseResult_25 = cond_br %68, %67 {handshake.bb = 6 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %68, %61 {handshake.bb = 6 : ui32, handshake.name = "cond_br12"} : <i1>, <f32>
    %trueResult_28, %falseResult_29 = cond_br %68, %result_22 {handshake.bb = 6 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %69 = merge %falseResult_27 {handshake.bb = 7 : ui32, handshake.name = "merge9"} : <f32>
    %result_30, %index_31 = control_merge [%falseResult_29]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    end {handshake.bb = 7 : ui32, handshake.name = "end0"} %69, %memEnd, %arg2 : <f32>, <>, <>
  }
}

