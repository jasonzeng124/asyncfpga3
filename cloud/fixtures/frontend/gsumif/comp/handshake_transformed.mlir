module {
  handshake.func @gsumif(%arg0: memref<1000xf32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["out0", "a_end", "end"]} {
    %0:4 = fork [4] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg0 : memref<1000xf32>] %arg1 (%addressResult) %result_30 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %1 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0.000000e+00 : f32} : <>, <f32>
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i1> to <i10>
    %5 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <f32>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %7 = mux %10#0 [%4, %trueResult_24] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i10>, <i10>] to <i10>
    %8:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i10>
    %9 = mux %10#1 [%5, %trueResult_26] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%6, %trueResult_28]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = 0.000000e+00 : f32} : <>, <f32>
    %addressResult, %dataResult = load[%8#0] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <f32>, <i10>, <f32>
    %13:2 = fork [2] %dataResult {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <f32>
    %14 = cmpf ult, %13#0, %12 {handshake.bb = 1 : ui32, handshake.name = "cmpf0"} : <f32>
    %15:4 = fork [4] %14 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult, %falseResult = cond_br %15#3, %9 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <f32>
    %trueResult_0, %falseResult_1 = cond_br %15#0, %8#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i10>
    %trueResult_2, %falseResult_3 = cond_br %15#2, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %trueResult_4, %falseResult_5 = cond_br %15#1, %13#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    sink %trueResult_4 {handshake.name = "sink0"} : <f32>
    %16 = merge %falseResult_1 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i10>
    %17:2 = fork [2] %16 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i10>
    %18 = merge %falseResult {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <f32>
    %19 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <f32>
    %result_6, %index_7 = control_merge [%falseResult_3]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink1"} : <i1>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 5 : i10} : <>, <i10>
    %22 = cmpi ugt, %17#1, %21 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i10>
    %23:4 = fork [4] %22 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %23#0, %17#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i10>
    %24 = trunci %falseResult_9 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i10> to <i3>
    %trueResult_10, %falseResult_11 = cond_br %23#1, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <f32>
    %trueResult_12, %falseResult_13 = cond_br %23#2, %19 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <f32>
    %trueResult_14, %falseResult_15 = cond_br %23#3, %result_6 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %25 = merge %trueResult_8 {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <i10>
    %26 = merge %trueResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <f32>
    %27 = merge %trueResult_12 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <f32>
    %28:3 = fork [3] %27 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <f32>
    %result_16, %index_17 = control_merge [%trueResult_14]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_17 {handshake.name = "sink2"} : <i1>
    %29 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %30 = constant %29 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 1.250000e-01 : f32} : <>, <f32>
    %31 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %32 = constant %31 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 5.000000e-01 : f32} : <>, <f32>
    %33 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %34 = constant %33 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 2.500000e-01 : f32} : <>, <f32>
    %35 = addf %28#2, %34 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf0"} : <f32>
    %36 = mulf %35, %28#1 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf0"} : <f32>
    %37 = addf %36, %32 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf1"} : <f32>
    %38 = mulf %37, %28#0 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf1"} : <f32>
    %39 = addf %38, %30 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf2"} : <f32>
    %40 = br %39 {handshake.bb = 3 : ui32, handshake.name = "br7"} : <f32>
    %41 = br %25 {handshake.bb = 3 : ui32, handshake.name = "br8"} : <i10>
    %42 = br %26 {handshake.bb = 3 : ui32, handshake.name = "br9"} : <f32>
    %43 = br %result_16 {handshake.bb = 3 : ui32, handshake.name = "br10"} : <>
    %44 = merge %24 {handshake.bb = 4 : ui32, handshake.name = "merge6"} : <i3>
    %45 = merge %falseResult_11 {handshake.bb = 4 : ui32, handshake.name = "merge7"} : <f32>
    %46 = merge %falseResult_13 {handshake.bb = 4 : ui32, handshake.name = "merge8"} : <f32>
    %47:3 = fork [3] %46 {handshake.bb = 4 : ui32, handshake.name = "fork8"} : <f32>
    %result_18, %index_19 = control_merge [%falseResult_15]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_19 {handshake.name = "sink3"} : <i1>
    %48 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %49 = constant %48 {handshake.bb = 4 : ui32, handshake.name = "constant16", value = 2.100000e-01 : f32} : <>, <f32>
    %50 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %51 = constant %50 {handshake.bb = 4 : ui32, handshake.name = "constant17", value = 0.699999988 : f32} : <>, <f32>
    %52 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %53 = constant %52 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 6.400000e-01 : f32} : <>, <f32>
    %54 = addf %47#2, %53 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "addf3"} : <f32>
    %55 = mulf %54, %47#1 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "mulf2"} : <f32>
    %56 = addf %55, %51 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "addf4"} : <f32>
    %57 = mulf %56, %47#0 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "mulf3"} : <f32>
    %58 = addf %57, %49 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "addf5"} : <f32>
    %59 = br %58 {handshake.bb = 4 : ui32, handshake.name = "br11"} : <f32>
    %60 = br %44 {handshake.bb = 4 : ui32, handshake.name = "br12"} : <i3>
    %61 = extui %60 {handshake.bb = 4 : ui32, handshake.name = "extui2"} : <i3> to <i10>
    %62 = br %45 {handshake.bb = 4 : ui32, handshake.name = "br13"} : <f32>
    %63 = br %result_18 {handshake.bb = 4 : ui32, handshake.name = "br14"} : <>
    %64 = mux %67#1 [%40, %59] {handshake.bb = 5 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %65 = mux %67#0 [%41, %61] {handshake.bb = 5 : ui32, handshake.name = "mux3"} : <i1>, [<i10>, <i10>] to <i10>
    %66 = mux %67#2 [%42, %62] {handshake.bb = 5 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %result_20, %index_21 = control_merge [%43, %63]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %67:3 = fork [3] %index_21 {handshake.bb = 5 : ui32, handshake.name = "fork9"} : <i1>
    %68 = addf %66, %64 {fastmath = #arith.fastmath<none>, handshake.bb = 5 : ui32, handshake.name = "addf6"} : <f32>
    %69 = br %68 {handshake.bb = 5 : ui32, handshake.name = "br15"} : <f32>
    %70 = br %65 {handshake.bb = 5 : ui32, handshake.name = "br16"} : <i10>
    %71 = br %result_20 {handshake.bb = 5 : ui32, handshake.name = "br17"} : <>
    %72 = mux %76#1 [%trueResult, %69] {handshake.bb = 6 : ui32, handshake.name = "mux5"} : <i1>, [<f32>, <f32>] to <f32>
    %73 = mux %76#0 [%trueResult_0, %70] {handshake.bb = 6 : ui32, handshake.name = "mux6"} : <i1>, [<i10>, <i10>] to <i10>
    %74 = extui %73 {handshake.bb = 6 : ui32, handshake.name = "extui3"} : <i10> to <i11>
    %75 = constant %78 {handshake.bb = 6 : ui32, handshake.name = "constant4", value = 1 : i11} : <>, <i11>
    %result_22, %index_23 = control_merge [%trueResult_2, %71]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %76:2 = fork [2] %index_23 {handshake.bb = 6 : ui32, handshake.name = "fork10"} : <i1>
    %77 = source {handshake.bb = 6 : ui32, handshake.name = "source8"} : <>
    %78 = source {handshake.bb = 6 : ui32, handshake.name = "source9"} : <>
    %79 = addi %74, %75 {handshake.bb = 6 : ui32, handshake.name = "addi0"} : <i11>
    %80:2 = fork [2] %79 {handshake.bb = 6 : ui32, handshake.name = "fork11"} : <i11>
    %81 = trunci %80#0 {handshake.bb = 6 : ui32, handshake.name = "trunci1"} : <i11> to <i10>
    %82 = constant %77 {handshake.bb = 6 : ui32, handshake.name = "constant5", value = 1000 : i11} : <>, <i11>
    %83 = cmpi ult, %80#1, %82 {handshake.bb = 6 : ui32, handshake.name = "cmpi1"} : <i11>
    %84:3 = fork [3] %83 {handshake.bb = 6 : ui32, handshake.name = "fork12"} : <i1>
    %trueResult_24, %falseResult_25 = cond_br %84#0, %81 {handshake.bb = 6 : ui32, handshake.name = "cond_br11"} : <i1>, <i10>
    sink %falseResult_25 {handshake.name = "sink4"} : <i10>
    %trueResult_26, %falseResult_27 = cond_br %84#1, %72 {handshake.bb = 6 : ui32, handshake.name = "cond_br12"} : <i1>, <f32>
    %trueResult_28, %falseResult_29 = cond_br %84#2, %result_22 {handshake.bb = 6 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %85 = merge %falseResult_27 {handshake.bb = 7 : ui32, handshake.name = "merge9"} : <f32>
    %result_30, %index_31 = control_merge [%falseResult_29]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    sink %index_31 {handshake.name = "sink5"} : <i1>
    end {handshake.bb = 7 : ui32, handshake.name = "end0"} %85, %memEnd, %0#1 : <f32>, <>, <>
  }
}

