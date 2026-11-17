module {
  handshake.func @bicg_float(%arg0: memref<900xf32>, %arg1: memref<30xf32>, %arg2: memref<30xf32>, %arg3: memref<30xf32>, %arg4: memref<30xf32>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, ...) -> (!handshake.channel<f32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "s", "q", "p", "r", "A_start", "s_start", "q_start", "p_start", "r_start", "start"], resNames = ["out0", "A_end", "s_end", "q_end", "p_end", "r_end", "end"]} {
    %0:3 = fork [3] %arg10 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg4 : memref<30xf32>] %arg9 (%addressResult_12) %82#4 {connectedBlocks = [2 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i5>) -> !handshake.channel<f32>
    %outputs_0, %memEnd_1 = mem_controller[%arg3 : memref<30xf32>] %arg8 (%addressResult_16) %82#3 {connectedBlocks = [2 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i5>) -> !handshake.channel<f32>
    %outputs_2, %memEnd_3 = mem_controller[%arg2 : memref<30xf32>] %arg7 (%addressResult, %72, %addressResult_30, %dataResult_31) %82#2 {connectedBlocks = [1 : i32, 3 : i32], handshake.name = "mem_controller6"} :    (!handshake.channel<i5>, !handshake.channel<i32>, !handshake.channel<i5>, !handshake.channel<f32>) -> !handshake.channel<f32>
    %1:2 = lsq[%arg1 : memref<30xf32>] (%arg6, %31#0, %addressResult_10, %addressResult_14, %dataResult_15, %82#1)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.control<>)
    %outputs_4, %memEnd_5 = mem_controller[%arg0 : memref<900xf32>] %arg5 (%addressResult_8) %82#0 {connectedBlocks = [2 : i32], handshake.name = "mem_controller7"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui8"} : <i1> to <i5>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %6 = mux %index [%4, %trueResult_32] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %7:4 = fork [4] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %result, %index = control_merge [%5, %trueResult_34]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %addressResult, %dataResult = load[%7#2] %outputs_2 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i5>, <f32>, <i5>, <f32>
    %9 = br %dataResult {handshake.bb = 1 : ui32, handshake.name = "br4"} : <f32>
    %10 = constant %8#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %11 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i1>
    %12 = extui %11 {handshake.bb = 2 : ui32, handshake.name = "extui9"} : <i1> to <i5>
    %13 = br %7#3 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i5>
    %14 = br %7#0 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i5>
    %15 = br %7#1 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i5>
    %16 = br %8#1 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %17 = mux %30#4 [%9, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %18 = mux %30#3 [%12, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i5>, <i5>] to <i5>
    %19:5 = fork [5] %18 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i5>
    %20 = extui %19#0 {handshake.bb = 2 : ui32, handshake.name = "extui10"} : <i5> to <i10>
    %21 = extui %19#4 {handshake.bb = 2 : ui32, handshake.name = "extui11"} : <i5> to <i6>
    %22 = constant %33 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i6} : <>, <i6>
    %23 = mux %30#2 [%13, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i5>, <i5>] to <i5>
    %24 = mux %30#0 [%14, %trueResult_22] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i5>, <i5>] to <i5>
    %25:2 = fork [2] %24 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i5>
    %26 = extui %25#1 {handshake.bb = 2 : ui32, handshake.name = "extui12"} : <i5> to <i64>
    %27:4 = fork [4] %26 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i64>
    %28 = mux %30#1 [%15, %trueResult_24] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i5>, <i5>] to <i5>
    %29:2 = fork [2] %28 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i5>
    %result_6, %index_7 = control_merge [%16, %trueResult_26]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %30:5 = fork [5] %index_7 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i1>
    %31:2 = fork [2] %result_6 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <>
    %32 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %33 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %34 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %35 = constant %34 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %36 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %37 = constant %36 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 3 : i64} : <>, <i64>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %39 = constant %38 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 2 : i64} : <>, <i64>
    %40 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %41 = constant %40 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i64} : <>, <i64>
    %42 = shli %27#0, %41 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %43 = trunci %42 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i64> to <i10>
    %44 = shli %27#1, %39 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %45 = trunci %44 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i10>
    %46 = addi %43, %45 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i10>
    %47 = shli %27#2, %37 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %48 = trunci %47 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i64> to <i10>
    %49 = shli %27#3, %35 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %50 = trunci %49 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i64> to <i10>
    %51 = addi %48, %50 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i10>
    %52 = addi %46, %51 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i10>
    %53 = addi %52, %20 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i10>
    %addressResult_8, %dataResult_9 = load[%53] %outputs_4 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <f32>, <i10>, <f32>
    %54:2 = fork [2] %dataResult_9 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <f32>
    %addressResult_10, %dataResult_11 = load[%19#3] %1#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load2"} : <i5>, <f32>, <i5>, <f32>
    %addressResult_12, %dataResult_13 = load[%29#0] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i5>, <f32>, <i5>, <f32>
    %55 = mulf %dataResult_13, %54#0 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %56 = addf %dataResult_11, %55 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf0"} : <f32>
    %addressResult_14, %dataResult_15 = store[%19#2] %56 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store4"} : <i5>, <f32>, <i5>, <f32>
    %addressResult_16, %dataResult_17 = load[%19#1] %outputs_0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load5"} : <i5>, <f32>, <i5>, <f32>
    %57 = mulf %54#1, %dataResult_17 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf1"} : <f32>
    %58 = addf %17, %57 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "addf1"} : <f32>
    %59 = addi %21, %22 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i6>
    %60:2 = fork [2] %59 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i6>
    %61 = trunci %60#0 {handshake.bb = 2 : ui32, handshake.name = "trunci4"} : <i6> to <i5>
    %62 = constant %32 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 30 : i6} : <>, <i6>
    %63 = cmpi ult, %60#1, %62 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i6>
    %64:6 = fork [6] %63 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult, %falseResult = cond_br %64#4, %58 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <f32>
    %trueResult_18, %falseResult_19 = cond_br %64#0, %61 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i5>
    sink %falseResult_19 {handshake.name = "sink0"} : <i5>
    %trueResult_20, %falseResult_21 = cond_br %64#3, %23 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i5>
    %trueResult_22, %falseResult_23 = cond_br %64#1, %25#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    sink %falseResult_23 {handshake.name = "sink1"} : <i5>
    %trueResult_24, %falseResult_25 = cond_br %64#2, %29#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i5>
    sink %falseResult_25 {handshake.name = "sink2"} : <i5>
    %trueResult_26, %falseResult_27 = cond_br %64#5, %31#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %65 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <f32>
    %66:2 = fork [2] %65 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <f32>
    %67 = merge %falseResult_21 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i5>
    %68:2 = fork [2] %67 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i5>
    %69 = extui %68#1 {handshake.bb = 3 : ui32, handshake.name = "extui13"} : <i5> to <i6>
    %70 = constant %74 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = 1 : i6} : <>, <i6>
    %result_28, %index_29 = control_merge [%falseResult_27]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_29 {handshake.name = "sink3"} : <i1>
    %71:2 = fork [2] %result_28 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <>
    %72 = constant %71#0 {handshake.bb = 3 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %73 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %74 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %addressResult_30, %dataResult_31 = store[%68#0] %66#0 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store6"} : <i5>, <f32>, <i5>, <f32>
    %75 = addi %69, %70 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i6>
    %76:2 = fork [2] %75 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i6>
    %77 = trunci %76#0 {handshake.bb = 3 : ui32, handshake.name = "trunci5"} : <i6> to <i5>
    %78 = constant %73 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 30 : i6} : <>, <i6>
    %79 = cmpi ult, %76#1, %78 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i6>
    %80:3 = fork [3] %79 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i1>
    %trueResult_32, %falseResult_33 = cond_br %80#0, %77 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i5>
    sink %falseResult_33 {handshake.name = "sink4"} : <i5>
    %trueResult_34, %falseResult_35 = cond_br %80#1, %71#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %trueResult_36, %falseResult_37 = cond_br %80#2, %66#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <f32>
    sink %trueResult_36 {handshake.name = "sink5"} : <f32>
    %81 = merge %falseResult_37 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <f32>
    %result_38, %index_39 = control_merge [%falseResult_35]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_39 {handshake.name = "sink6"} : <i1>
    %82:5 = fork [5] %result_38 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %81, %memEnd_5, %1#1, %memEnd_3, %memEnd_1, %memEnd, %0#1 : <f32>, <>, <>, <>, <>, <>, <>
  }
}

