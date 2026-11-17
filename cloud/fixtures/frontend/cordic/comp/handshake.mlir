module {
  handshake.func @cordic(%arg0: !handshake.channel<f32>, %arg1: memref<2xf32>, %arg2: memref<1000xf32>, %arg3: !handshake.channel<f32>, %arg4: !handshake.channel<f32>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["theta", "a", "cordic_phase", "current_cos", "current_sin", "a_start", "cordic_phase_start", "start"], resNames = ["out0", "a_end", "cordic_phase_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg2 : memref<1000xf32>] %arg6 (%addressResult) %result_11 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<f32>
    %memEnd_0 = mem_controller[%arg1 : memref<2xf32>] %arg5 (%40, %addressResult_13, %dataResult_14, %addressResult_15, %dataResult_16) %result_11 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.channel<i32>, !handshake.channel<f32>) -> ()
    %0 = constant %arg7 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg7 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1.000000e+00 : f32} : <>, <f32>
    %2 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <f32>
    %3 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %4 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <f32>
    %5 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <f32>
    %6 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <f32>
    %7 = br %arg7 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %8 = mux %index [%2, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %9 = mux %index [%3, %trueResult_1] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %index [%4, %trueResult_3] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %11 = mux %index [%5, %trueResult_5] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<f32>, <f32>] to <f32>
    %12 = mux %index [%6, %trueResult_7] {handshake.bb = 1 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%7, %trueResult_9]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 1000 : i32} : <>, <i32>
    %15 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %16 = constant %15 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = -1.000000e+00 : f32} : <>, <f32>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %20 = constant %19 {handshake.bb = 1 : ui32, handshake.name = "constant12", value = 0.000000e+00 : f32} : <>, <f32>
    %21 = source {handshake.bb = 1 : ui32, handshake.name = "source4"} : <>
    %22 = constant %21 {handshake.bb = 1 : ui32, handshake.name = "constant13", value = 5.000000e-01 : f32} : <>, <f32>
    %23 = source {handshake.bb = 1 : ui32, handshake.name = "source5"} : <>
    %24 = constant %23 {handshake.bb = 1 : ui32, handshake.name = "constant14", value = 1.000000e+00 : f32} : <>, <f32>
    %25 = mulf %10, %22 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf0"} : <f32>
    %26 = cmpf olt, %8, %20 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %27 = select %26[%18, %24] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <f32>
    %28 = extui %9 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %29 = trunci %28 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%29] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %30 = mulf %27, %dataResult {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf1"} : <f32>
    %31 = subf %8, %30 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "subf0"} : <f32>
    %32 = mulf %11, %27 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf2"} : <f32>
    %33 = mulf %32, %10 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf3"} : <f32>
    %34 = addf %33, %12 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf0"} : <f32>
    %35 = mulf %12, %27 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf4"} : <f32>
    %36 = mulf %35, %10 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf5"} : <f32>
    %37 = subf %11, %36 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "subf1"} : <f32>
    %38 = addi %9, %16 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %39 = cmpi ult, %38, %14 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %39, %31 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <f32>
    %trueResult_1, %falseResult_2 = cond_br %39, %38 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_3, %falseResult_4 = cond_br %39, %25 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <f32>
    %trueResult_5, %falseResult_6 = cond_br %39, %37 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <f32>
    %trueResult_7, %falseResult_8 = cond_br %39, %34 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <f32>
    %trueResult_9, %falseResult_10 = cond_br %39, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %40 = constant %result_11 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = 2 : i32} : <>, <i32>
    %41 = merge %falseResult_8 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    %42 = merge %falseResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <f32>
    %43 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <f32>
    %result_11, %index_12 = control_merge [%falseResult_10]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %44 = constant %result_11 {handshake.bb = 2 : ui32, handshake.name = "constant15", value = 0 : i32} : <>, <i32>
    %45 = constant %result_11 {handshake.bb = 2 : ui32, handshake.name = "constant16", value = 1 : i32} : <>, <i32>
    %addressResult_13, %dataResult_14 = store[%44] %42 {handshake.bb = 2 : ui32, handshake.name = "store1"} : <i32>, <f32>, <i32>, <f32>
    %addressResult_15, %dataResult_16 = store[%45] %41 {handshake.bb = 2 : ui32, handshake.name = "store2"} : <i32>, <f32>, <i32>, <f32>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %43, %memEnd_0, %memEnd, %arg7 : <f32>, <>, <>, <>
  }
}

