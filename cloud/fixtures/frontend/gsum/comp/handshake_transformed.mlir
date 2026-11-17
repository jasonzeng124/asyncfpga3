module {
  handshake.func @gsum(%arg0: memref<1000xf32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %0:4 = fork [4] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg0 : memref<1000xf32>] %arg1 (%addressResult) %result_16 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %1 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0.000000e+00 : f32} : <>, <f32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <f32>
    %3 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %5 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i1> to <i10>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %7 = mux %10#1 [%2, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<f32>, <f32>] to <f32>
    %8 = mux %10#0 [%5, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i10>, <i10>] to <i10>
    %9:2 = fork [2] %8 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i10>
    %result, %index = control_merge [%6, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0.000000e+00 : f32} : <>, <f32>
    %addressResult, %dataResult = load[%9#0] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <f32>, <i10>, <f32>
    %13:2 = fork [2] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <f32>
    %14 = cmpf ult, %13#0, %12 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %15:4 = fork [4] %14 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult, %falseResult = cond_br %15#3, %7 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <f32>
    %trueResult_0, %falseResult_1 = cond_br %15#0, %9#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i10>
    %trueResult_2, %falseResult_3 = cond_br %15#2, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %trueResult_4, %falseResult_5 = cond_br %15#1, %13#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <f32>
    sink %trueResult_4 {handshake.name = "sink0"} : <f32>
    %16 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    %17 = merge %falseResult_1 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i10>
    %18 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <f32>
    %19:5 = fork [5] %18 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <f32>
    %result_6, %index_7 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink1"} : <i1>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 3.300000e-01 : f32} : <>, <f32>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %23 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 2.100000e-01 : f32} : <>, <f32>
    %24 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %25 = constant %24 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 0.699999988 : f32} : <>, <f32>
    %26 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %27 = constant %26 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 6.400000e-01 : f32} : <>, <f32>
    %28 = addf %19#4, %27 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf0"} : <f32>
    %29 = mulf %28, %19#3 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %30 = addf %29, %25 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf1"} : <f32>
    %31 = mulf %30, %19#2 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf1"} : <f32>
    %32 = addf %31, %23 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf2"} : <f32>
    %33 = mulf %32, %19#1 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf2"} : <f32>
    %34 = addf %33, %21 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf3"} : <f32>
    %35 = mulf %34, %19#0 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf3"} : <f32>
    %36 = addf %16, %35 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf4"} : <f32>
    %37 = br %36 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <f32>
    %38 = br %17 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <i10>
    %39 = br %result_6 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <>
    %40 = mux %44#1 [%trueResult, %37] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %41 = mux %44#0 [%trueResult_0, %38] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i10>, <i10>] to <i10>
    %42 = extui %41 {handshake.bb = 3 : ui32, handshake.name = "extui2"} : <i10> to <i11>
    %43 = constant %46 {handshake.bb = 3 : ui32, handshake.name = "constant3", value = 1 : i11} : <>, <i11>
    %result_8, %index_9 = control_merge [%trueResult_2, %39]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %44:2 = fork [2] %index_9 {handshake.bb = 3 : ui32, handshake.name = "fork6"} : <i1>
    %45 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %46 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %47 = addi %42, %43 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i11>
    %48:2 = fork [2] %47 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i11>
    %49 = trunci %48#0 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i11> to <i10>
    %50 = constant %45 {handshake.bb = 3 : ui32, handshake.name = "constant4", value = 1000 : i11} : <>, <i11>
    %51 = cmpi ult, %48#1, %50 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i11>
    %52:3 = fork [3] %51 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_10, %falseResult_11 = cond_br %52#1, %40 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %trueResult_12, %falseResult_13 = cond_br %52#0, %49 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i10>
    sink %falseResult_13 {handshake.name = "sink2"} : <i10>
    %trueResult_14, %falseResult_15 = cond_br %52#2, %result_8 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %53 = merge %falseResult_11 {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <f32>
    %result_16, %index_17 = control_merge [%falseResult_15]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_17 {handshake.name = "sink3"} : <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %53, %memEnd, %0#1 : <f32>, <>, <>
  }
}

