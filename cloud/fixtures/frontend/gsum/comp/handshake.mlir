module {
  handshake.func @gsum(%arg0: memref<1000xf32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<1000xf32>] %arg1 (%addressResult) %result_16 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0.000000e+00 : f32} : <>, <f32>
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %2 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <f32>
    %3 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %4 = br %arg2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %5 = mux %index [%2, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %6 = mux %index [%3, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0.000000e+00 : f32} : <>, <f32>
    %9 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = trunci %9 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%10] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %11 = cmpf ult, %dataResult, %8 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %trueResult, %falseResult = cond_br %11, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <f32>
    %trueResult_0, %falseResult_1 = cond_br %11, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %11, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %trueResult_4, %falseResult_5 = cond_br %11, %dataResult {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <f32>
    %12 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    %13 = merge %falseResult_1 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %14 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <f32>
    %result_6, %index_7 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %15 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %16 = constant %15 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 3.300000e-01 : f32} : <>, <f32>
    %17 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %18 = constant %17 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 2.100000e-01 : f32} : <>, <f32>
    %19 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %20 = constant %19 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 0.699999988 : f32} : <>, <f32>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 6.400000e-01 : f32} : <>, <f32>
    %23 = addf %14, %22 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf0"} : <f32>
    %24 = mulf %23, %14 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %25 = addf %24, %20 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf1"} : <f32>
    %26 = mulf %25, %14 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf1"} : <f32>
    %27 = addf %26, %18 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf2"} : <f32>
    %28 = mulf %27, %14 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf2"} : <f32>
    %29 = addf %28, %16 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf3"} : <f32>
    %30 = mulf %29, %14 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf3"} : <f32>
    %31 = addf %12, %30 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf4"} : <f32>
    %32 = br %31 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <f32>
    %33 = br %13 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <i32>
    %34 = br %result_6 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <>
    %35 = mux %index_9 [%trueResult, %32] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %36 = mux %index_9 [%trueResult_0, %33] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_8, %index_9 = control_merge [%trueResult_2, %34]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %37 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %38 = constant %37 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 1000 : i32} : <>, <i32>
    %39 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %40 = constant %39 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 1 : i32} : <>, <i32>
    %41 = addi %36, %40 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %42 = cmpi ult, %41, %38 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %42, %35 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %trueResult_12, %falseResult_13 = cond_br %42, %41 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %42, %result_8 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %43 = merge %falseResult_11 {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <f32>
    %result_16, %index_17 = control_merge [%falseResult_15]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %43, %memEnd, %arg2 : <f32>, <>, <>
  }
}

