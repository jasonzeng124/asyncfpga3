module {
  handshake.func @atax_float(%arg0: memref<400xf32>, %arg1: memref<20xf32>, %arg2: memref<20xf32>, %arg3: memref<20xf32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "x", "y", "tmp", "A_start", "x_start", "y_start", "tmp_start", "start"], resNames = ["A_end", "x_end", "y_end", "tmp_end", "end"]} {
    %0:3 = fork [3] %arg8 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg3 : memref<20xf32>] %arg7 (%addressResult, %99, %addressResult_40, %dataResult_41) %108#3 {connectedBlocks = [1 : i32, 5 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i5>, !handshake.channel<i32>, !handshake.channel<i5>, !handshake.channel<f32>) -> !handshake.channel<f32>
    %1:2 = lsq[%arg2 : memref<20xf32>] (%arg6, %72#0, %addressResult_22, %addressResult_26, %dataResult_27, %108#2)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.control<>)
    %outputs_0, %memEnd_1 = mem_controller[%arg1 : memref<20xf32>] %arg5 (%addressResult_8) %108#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i5>) -> !handshake.channel<f32>
    %outputs_2:2, %memEnd_3 = mem_controller[%arg0 : memref<400xf32>] %arg4 (%addressResult_6, %addressResult_24) %108#0 {connectedBlocks = [2 : i32, 4 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i9>, !handshake.channel<i9>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui9"} : <i1> to <i5>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %6 = mux %index [%4, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %7:3 = fork [3] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %result, %index = control_merge [%5, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %addressResult, %dataResult = load[%7#1] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i5>, <f32>, <i5>, <f32>
    %9 = br %dataResult {handshake.bb = 1 : ui32, handshake.name = "br5"} : <f32>
    %10 = constant %8#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %11 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i1>
    %12 = extui %11 {handshake.bb = 2 : ui32, handshake.name = "extui10"} : <i1> to <i5>
    %13 = br %7#2 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i5>
    %14 = br %7#0 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i5>
    %15 = br %8#1 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %16 = mux %27#3 [%9, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %17 = mux %27#2 [%12, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i5>, <i5>] to <i5>
    %18:3 = fork [3] %17 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i5>
    %19 = extui %18#0 {handshake.bb = 2 : ui32, handshake.name = "extui11"} : <i5> to <i9>
    %20 = extui %18#2 {handshake.bb = 2 : ui32, handshake.name = "extui12"} : <i5> to <i6>
    %21 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i6} : <>, <i6>
    %22 = mux %27#1 [%13, %trueResult_12] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i5>, <i5>] to <i5>
    %23 = mux %27#0 [%14, %trueResult_14] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i5>, <i5>] to <i5>
    %24:2 = fork [2] %23 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i5>
    %25 = extui %24#1 {handshake.bb = 2 : ui32, handshake.name = "extui13"} : <i5> to <i64>
    %26:2 = fork [2] %25 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i64>
    %result_4, %index_5 = control_merge [%15, %trueResult_16]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %27:4 = fork [4] %index_5 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i1>
    %28 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %30 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %31 = constant %30 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 4 : i64} : <>, <i64>
    %32 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %33 = constant %32 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 2 : i64} : <>, <i64>
    %34 = shli %26#0, %33 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %35 = trunci %34 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i64> to <i9>
    %36 = shli %26#1, %31 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %37 = trunci %36 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i9>
    %38 = addi %35, %37 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i9>
    %39 = addi %38, %19 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i9>
    %addressResult_6, %dataResult_7 = load[%39] %outputs_2#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i9>, <f32>, <i9>, <f32>
    %addressResult_8, %dataResult_9 = load[%18#1] %outputs_0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i5>, <f32>, <i5>, <f32>
    %40 = mulf %dataResult_7, %dataResult_9 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %41 = addf %16, %40 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf0"} : <f32>
    %42 = addi %20, %21 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i6>
    %43:2 = fork [2] %42 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i6>
    %44 = trunci %43#0 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i6> to <i5>
    %45 = constant %28 {handshake.bb = 2 : ui32, handshake.name = "constant18", value = 20 : i6} : <>, <i6>
    %46 = cmpi ult, %43#1, %45 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i6>
    %47:5 = fork [5] %46 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult, %falseResult = cond_br %47#3, %41 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <f32>
    %trueResult_10, %falseResult_11 = cond_br %47#0, %44 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i5>
    sink %falseResult_11 {handshake.name = "sink0"} : <i5>
    %trueResult_12, %falseResult_13 = cond_br %47#2, %22 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    %trueResult_14, %falseResult_15 = cond_br %47#1, %24#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i5>
    sink %falseResult_15 {handshake.name = "sink1"} : <i5>
    %trueResult_16, %falseResult_17 = cond_br %47#4, %result_4 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %48 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <f32>
    %49 = merge %falseResult_13 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i5>
    %50:2 = fork [2] %49 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i5>
    %result_18, %index_19 = control_merge [%falseResult_17]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_19 {handshake.name = "sink2"} : <i1>
    %51:2 = fork [2] %result_18 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <>
    %52 = constant %51#0 {handshake.bb = 3 : ui32, handshake.name = "constant19", value = false} : <>, <i1>
    %53 = br %52 {handshake.bb = 3 : ui32, handshake.name = "br10"} : <i1>
    %54 = extui %53 {handshake.bb = 4 : ui32, handshake.name = "extui14"} : <i1> to <i5>
    %55 = br %50#1 {handshake.bb = 3 : ui32, handshake.name = "br11"} : <i5>
    %56 = br %48 {handshake.bb = 3 : ui32, handshake.name = "br12"} : <f32>
    %57 = br %50#0 {handshake.bb = 3 : ui32, handshake.name = "br13"} : <i5>
    %58 = br %51#1 {handshake.bb = 3 : ui32, handshake.name = "br14"} : <>
    %59 = mux %71#2 [%54, %trueResult_28] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i5>, <i5>] to <i5>
    %60:4 = fork [4] %59 {handshake.bb = 4 : ui32, handshake.name = "fork11"} : <i5>
    %61 = extui %60#0 {handshake.bb = 4 : ui32, handshake.name = "extui15"} : <i5> to <i9>
    %62 = extui %60#3 {handshake.bb = 4 : ui32, handshake.name = "extui16"} : <i5> to <i6>
    %63 = constant %74 {handshake.bb = 4 : ui32, handshake.name = "constant20", value = 1 : i6} : <>, <i6>
    %64 = mux %71#1 [%55, %trueResult_30] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i5>, <i5>] to <i5>
    %65 = mux %71#3 [%56, %trueResult_32] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<f32>, <f32>] to <f32>
    %66:2 = fork [2] %65 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <f32>
    %67 = mux %71#0 [%57, %trueResult_34] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i5>, <i5>] to <i5>
    %68:2 = fork [2] %67 {handshake.bb = 4 : ui32, handshake.name = "fork13"} : <i5>
    %69 = extui %68#1 {handshake.bb = 4 : ui32, handshake.name = "extui17"} : <i5> to <i64>
    %70:2 = fork [2] %69 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i64>
    %result_20, %index_21 = control_merge [%58, %trueResult_36]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %71:4 = fork [4] %index_21 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i1>
    %72:2 = fork [2] %result_20 {handshake.bb = 4 : ui32, handshake.name = "fork16"} : <>
    %73 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %74 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %75 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %76 = constant %75 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 4 : i64} : <>, <i64>
    %77 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %78 = constant %77 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 2 : i64} : <>, <i64>
    %addressResult_22, %dataResult_23 = load[%60#2] %1#0 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load3"} : <i5>, <f32>, <i5>, <f32>
    %79 = shli %70#0, %78 {handshake.bb = 4 : ui32, handshake.name = "shli2"} : <i64>
    %80 = trunci %79 {handshake.bb = 4 : ui32, handshake.name = "trunci3"} : <i64> to <i9>
    %81 = shli %70#1, %76 {handshake.bb = 4 : ui32, handshake.name = "shli3"} : <i64>
    %82 = trunci %81 {handshake.bb = 4 : ui32, handshake.name = "trunci4"} : <i64> to <i9>
    %83 = addi %80, %82 {handshake.bb = 4 : ui32, handshake.name = "addi6"} : <i9>
    %84 = addi %83, %61 {handshake.bb = 4 : ui32, handshake.name = "addi2"} : <i9>
    %addressResult_24, %dataResult_25 = load[%84] %outputs_2#1 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : <i9>, <f32>, <i9>, <f32>
    %85 = mulf %dataResult_25, %66#1 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "mulf1"} : <f32>
    %86 = addf %dataResult_23, %85 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "addf1"} : <f32>
    %addressResult_26, %dataResult_27 = store[%60#1] %86 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store5"} : <i5>, <f32>, <i5>, <f32>
    %87 = addi %62, %63 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i6>
    %88:2 = fork [2] %87 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <i6>
    %89 = trunci %88#0 {handshake.bb = 4 : ui32, handshake.name = "trunci5"} : <i6> to <i5>
    %90 = constant %73 {handshake.bb = 4 : ui32, handshake.name = "constant21", value = 20 : i6} : <>, <i6>
    %91 = cmpi ult, %88#1, %90 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i6>
    %92:5 = fork [5] %91 {handshake.bb = 4 : ui32, handshake.name = "fork18"} : <i1>
    %trueResult_28, %falseResult_29 = cond_br %92#0, %89 {handshake.bb = 4 : ui32, handshake.name = "cond_br8"} : <i1>, <i5>
    sink %falseResult_29 {handshake.name = "sink3"} : <i5>
    %trueResult_30, %falseResult_31 = cond_br %92#2, %64 {handshake.bb = 4 : ui32, handshake.name = "cond_br9"} : <i1>, <i5>
    %trueResult_32, %falseResult_33 = cond_br %92#3, %66#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <f32>
    %trueResult_34, %falseResult_35 = cond_br %92#1, %68#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i5>
    sink %falseResult_35 {handshake.name = "sink4"} : <i5>
    %trueResult_36, %falseResult_37 = cond_br %92#4, %72#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %93 = merge %falseResult_31 {handshake.bb = 5 : ui32, handshake.name = "merge2"} : <i5>
    %94:2 = fork [2] %93 {handshake.bb = 5 : ui32, handshake.name = "fork19"} : <i5>
    %95 = extui %94#1 {handshake.bb = 5 : ui32, handshake.name = "extui18"} : <i5> to <i6>
    %96 = constant %101 {handshake.bb = 5 : ui32, handshake.name = "constant22", value = 1 : i6} : <>, <i6>
    %97 = merge %falseResult_33 {handshake.bb = 5 : ui32, handshake.name = "merge3"} : <f32>
    %result_38, %index_39 = control_merge [%falseResult_37]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_39 {handshake.name = "sink5"} : <i1>
    %98:2 = fork [2] %result_38 {handshake.bb = 5 : ui32, handshake.name = "fork20"} : <>
    %99 = constant %98#0 {handshake.bb = 5 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %100 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %101 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %addressResult_40, %dataResult_41 = store[%94#0] %97 {handshake.bb = 5 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store6"} : <i5>, <f32>, <i5>, <f32>
    %102 = addi %95, %96 {handshake.bb = 5 : ui32, handshake.name = "addi4"} : <i6>
    %103:2 = fork [2] %102 {handshake.bb = 5 : ui32, handshake.name = "fork21"} : <i6>
    %104 = trunci %103#0 {handshake.bb = 5 : ui32, handshake.name = "trunci6"} : <i6> to <i5>
    %105 = constant %100 {handshake.bb = 5 : ui32, handshake.name = "constant23", value = 20 : i6} : <>, <i6>
    %106 = cmpi ult, %103#1, %105 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i6>
    %107:2 = fork [2] %106 {handshake.bb = 5 : ui32, handshake.name = "fork22"} : <i1>
    %trueResult_42, %falseResult_43 = cond_br %107#0, %104 {handshake.bb = 5 : ui32, handshake.name = "cond_br13"} : <i1>, <i5>
    sink %falseResult_43 {handshake.name = "sink6"} : <i5>
    %trueResult_44, %falseResult_45 = cond_br %107#1, %98#1 {handshake.bb = 5 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %result_46, %index_47 = control_merge [%falseResult_45]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_47 {handshake.name = "sink7"} : <i1>
    %108:4 = fork [4] %result_46 {handshake.bb = 6 : ui32, handshake.name = "fork23"} : <>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %memEnd_3, %memEnd_1, %1#1, %memEnd, %0#1 : <>, <>, <>, <>, <>
  }
}

