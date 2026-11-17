module {
  handshake.func @cordic(%arg0: !handshake.channel<f32>, %arg1: memref<2xf32>, %arg2: memref<1000xf32>, %arg3: !handshake.channel<f32>, %arg4: !handshake.channel<f32>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["theta", "a", "cordic_phase", "current_cos", "current_sin", "a_start", "cordic_phase_start", "start"], resNames = ["out0", "a_end", "cordic_phase_end", "end"]} {
    %0:4 = fork [4] %arg7 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg2 : memref<1000xf32>] %arg6 (%addressResult) %54#3 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %memEnd_0 = mem_controller[%arg1 : memref<2xf32>] %arg5 (%55, %addressResult_13, %dataResult_14, %addressResult_15, %dataResult_16) %54#2 {connectedBlocks = [2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i1>, !handshake.channel<f32>, !handshake.channel<i1>, !handshake.channel<f32>) -> ()
    %1 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1.000000e+00 : f32} : <>, <f32>
    %2 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <f32>
    %3 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %5 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i1> to <i10>
    %6 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <f32>
    %7 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <f32>
    %8 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <f32>
    %9 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %10 = mux %22#1 [%2, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %11:2 = fork [2] %10 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <f32>
    %12 = mux %22#0 [%5, %trueResult_1] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i10>, <i10>] to <i10>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i10>
    %14 = extui %13#1 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i10> to <i11>
    %15 = constant %24 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i11} : <>, <i11>
    %16 = mux %22#2 [%6, %trueResult_3] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %17:3 = fork [3] %16 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <f32>
    %18 = mux %22#3 [%7, %trueResult_5] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<f32>, <f32>] to <f32>
    %19:2 = fork [2] %18 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <f32>
    %20 = mux %22#4 [%8, %trueResult_7] {handshake.bb = 1 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %21:2 = fork [2] %20 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <f32>
    %result, %index = control_merge [%9, %trueResult_9]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %22:5 = fork [5] %index {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %23 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %24 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %25 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %26 = constant %25 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = -1.000000e+00 : f32} : <>, <f32>
    %27 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %28 = constant %27 {handshake.bb = 1 : ui32, handshake.name = "constant12", value = 0.000000e+00 : f32} : <>, <f32>
    %29 = source {handshake.bb = 1 : ui32, handshake.name = "source4"} : <>
    %30 = constant %29 {handshake.bb = 1 : ui32, handshake.name = "constant13", value = 5.000000e-01 : f32} : <>, <f32>
    %31 = source {handshake.bb = 1 : ui32, handshake.name = "source5"} : <>
    %32 = constant %31 {handshake.bb = 1 : ui32, handshake.name = "constant14", value = 1.000000e+00 : f32} : <>, <f32>
    %33 = mulf %17#2, %30 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf0"} : <f32>
    %34 = cmpf olt, %11#1, %28 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %35 = select %34[%26, %32] {handshake.bb = 1 : ui32, handshake.name = "select0"} : <i1>, <f32>
    %36:3 = fork [3] %35 {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <f32>
    %addressResult, %dataResult = load[%13#0] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <f32>, <i10>, <f32>
    %37 = mulf %36#2, %dataResult {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf1"} : <f32>
    %38 = subf %11#0, %37 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "subf0"} : <f32>
    %39 = mulf %19#1, %36#1 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf2"} : <f32>
    %40 = mulf %39, %17#1 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf3"} : <f32>
    %41 = addf %40, %21#1 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "addf0"} : <f32>
    %42 = mulf %21#0, %36#0 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf4"} : <f32>
    %43 = mulf %42, %17#0 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "mulf5"} : <f32>
    %44 = subf %19#0, %43 {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "subf1"} : <f32>
    %45 = addi %14, %15 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i11>
    %46:2 = fork [2] %45 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i11>
    %47 = trunci %46#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i11> to <i10>
    %48 = constant %23 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 1000 : i11} : <>, <i11>
    %49 = cmpi ult, %46#1, %48 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i11>
    %50:6 = fork [6] %49 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult, %falseResult = cond_br %50#1, %38 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <f32>
    %trueResult_1, %falseResult_2 = cond_br %50#0, %47 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i10>
    sink %falseResult_2 {handshake.name = "sink0"} : <i10>
    %trueResult_3, %falseResult_4 = cond_br %50#2, %33 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <f32>
    sink %falseResult_4 {handshake.name = "sink1"} : <f32>
    %trueResult_5, %falseResult_6 = cond_br %50#3, %44 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <f32>
    %trueResult_7, %falseResult_8 = cond_br %50#4, %41 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <f32>
    %trueResult_9, %falseResult_10 = cond_br %50#5, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %51 = merge %falseResult_8 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    %52 = merge %falseResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <f32>
    %53 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <f32>
    %result_11, %index_12 = control_merge [%falseResult_10]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_12 {handshake.name = "sink2"} : <i1>
    %54:5 = fork [5] %result_11 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <>
    %55 = constant %54#4 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 2 : i32} : <>, <i32>
    %56 = constant %54#1 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = false} : <>, <i1>
    %addressResult_13, %dataResult_14 = store[%56] %52 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store1"} : <i1>, <f32>, <i1>, <f32>
    %57 = constant %54#0 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = true} : <>, <i1>
    %addressResult_15, %dataResult_16 = store[%57] %51 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i1>, <f32>, <i1>, <f32>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %53, %memEnd_0, %memEnd, %0#1 : <f32>, <>, <>, <>
  }
}

