module {
  handshake.func @stencil_2d(%arg0: memref<900xi32>, %arg1: memref<10xi32>, %arg2: memref<900xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["orig", "filter", "sol", "orig_start", "filter_start", "sol_start", "start"], resNames = ["out0", "orig_end", "filter_end", "sol_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg2 : memref<900xi32>] %arg5 (%91, %addressResult_33, %dataResult_34) %101#2 {connectedBlocks = [5 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<10xi32>] %arg4 (%addressResult) %101#1 {connectedBlocks = [3 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i4>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<900xi32>] %arg3 (%addressResult_7) %101#0 {connectedBlocks = [3 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %3 = extui %2 {handshake.bb = 0 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %5 = mux %index [%3, %trueResult_35] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_37]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <>
    %7 = constant %6#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %8 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i1>
    %9 = extui %8 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i1> to <i32>
    %10:2 = fork [2] %9 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i32>
    %11 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %12 = br %6#1 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <>
    %13 = mux %18#0 [%10#0, %trueResult_23] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %14:7 = fork [7] %13 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i32>
    %15 = mux %18#1 [%10#1, %trueResult_25] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %18#2 [%11, %trueResult_27] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %17:2 = fork [2] %16 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i32>
    %result_3, %index_4 = control_merge [%12, %trueResult_29]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %18:3 = fork [3] %index_4 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i1>
    %19:2 = fork [2] %result_3 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %22:2 = fork [2] %21 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i32>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 3 : i32} : <>, <i32>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i32} : <>, <i32>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %28 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 2 : i32} : <>, <i32>
    %29 = shli %14#6, %22#1 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i32>
    %30 = addi %14#5, %29 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i32>
    %31 = shli %14#4, %22#0 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i32>
    %32 = shli %14#3, %28 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i32>
    %33 = addi %31, %32 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i32>
    %34 = shli %14#2, %24 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i32>
    %35 = shli %14#1, %26 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i32>
    %36 = addi %34, %35 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i32>
    %37 = addi %33, %36 {handshake.bb = 2 : ui32, handshake.name = "addi10"} : <i32>
    %38 = addi %37, %17#1 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %39 = constant %19#0 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %40 = br %39 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <i1>
    %41 = extui %40 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i1> to <i32>
    %42 = br %15 {handshake.bb = 2 : ui32, handshake.name = "br9"} : <i32>
    %43 = br %17#0 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <i32>
    %44 = br %14#0 {handshake.bb = 2 : ui32, handshake.name = "br11"} : <i32>
    %45 = br %30 {handshake.bb = 2 : ui32, handshake.name = "br12"} : <i32>
    %46 = br %38 {handshake.bb = 2 : ui32, handshake.name = "br13"} : <i32>
    %47 = br %19#1 {handshake.bb = 2 : ui32, handshake.name = "br14"} : <>
    %48 = mux %61#0 [%41, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %49:3 = fork [3] %48 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i32>
    %50 = trunci %49#0 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i32> to <i4>
    %51 = trunci %49#1 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %52 = mux %61#1 [%42, %trueResult_9] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %53 = mux %61#2 [%43, %trueResult_11] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %54 = mux %61#3 [%44, %trueResult_13] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %55 = mux %61#4 [%45, %trueResult_15] {handshake.bb = 3 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %56:2 = fork [2] %55 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i32>
    %57 = trunci %56#0 {handshake.bb = 3 : ui32, handshake.name = "trunci2"} : <i32> to <i4>
    %58 = mux %61#5 [%46, %trueResult_17] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %59:2 = fork [2] %58 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %60 = trunci %59#0 {handshake.bb = 3 : ui32, handshake.name = "trunci3"} : <i32> to <i10>
    %result_5, %index_6 = control_merge [%47, %trueResult_19]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %61:6 = fork [6] %index_6 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i1>
    %62 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %63 = constant %62 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 1 : i32} : <>, <i32>
    %64 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %65 = constant %64 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 3 : i32} : <>, <i32>
    %66 = addi %57, %50 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i4>
    %addressResult, %dataResult = load[%66] %outputs {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i4>, <i32>, <i4>, <i32>
    %67 = addi %60, %51 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i10>
    %addressResult_7, %dataResult_8 = load[%67] %outputs_1 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %68 = muli %dataResult, %dataResult_8 {handshake.bb = 3 : ui32, handshake.name = "muli2"} : <i32>
    %69 = addi %52, %68 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %70 = addi %49#2, %63 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i32>
    %71:2 = fork [2] %70 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i32>
    %72 = cmpi ne, %71#1, %65 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i32>
    %73:7 = fork [7] %72 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i1>
    %trueResult, %falseResult = cond_br %73#6, %71#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_9, %falseResult_10 = cond_br %73#5, %69 {handshake.bb = 3 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %73#4, %53 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_13, %falseResult_14 = cond_br %73#3, %54 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_15, %falseResult_16 = cond_br %73#2, %56#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_16 {handshake.name = "sink1"} : <i32>
    %trueResult_17, %falseResult_18 = cond_br %73#1, %59#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_18 {handshake.name = "sink2"} : <i32>
    %trueResult_19, %falseResult_20 = cond_br %73#0, %result_5 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %74 = merge %falseResult_10 {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i32>
    %75 = merge %falseResult_12 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <i32>
    %76 = merge %falseResult_14 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i32>
    %result_21, %index_22 = control_merge [%falseResult_20]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_22 {handshake.name = "sink3"} : <i1>
    %77 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %78 = constant %77 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %79 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %80 = constant %79 {handshake.bb = 4 : ui32, handshake.name = "constant16", value = 3 : i32} : <>, <i32>
    %81 = addi %76, %78 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i32>
    %82:2 = fork [2] %81 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i32>
    %83 = cmpi ne, %82#1, %80 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i32>
    %84:4 = fork [4] %83 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i1>
    %trueResult_23, %falseResult_24 = cond_br %84#3, %82#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %falseResult_24 {handshake.name = "sink4"} : <i32>
    %trueResult_25, %falseResult_26 = cond_br %84#2, %74 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_27, %falseResult_28 = cond_br %84#1, %75 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_29, %falseResult_30 = cond_br %84#0, %result_21 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %85 = merge %falseResult_26 {handshake.bb = 5 : ui32, handshake.name = "merge3"} : <i32>
    %86:2 = fork [2] %85 {handshake.bb = 5 : ui32, handshake.name = "fork16"} : <i32>
    %87 = merge %falseResult_28 {handshake.bb = 5 : ui32, handshake.name = "merge4"} : <i32>
    %88:2 = fork [2] %87 {handshake.bb = 5 : ui32, handshake.name = "fork17"} : <i32>
    %89 = trunci %88#0 {handshake.bb = 5 : ui32, handshake.name = "trunci4"} : <i32> to <i10>
    %result_31, %index_32 = control_merge [%falseResult_30]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_32 {handshake.name = "sink5"} : <i1>
    %90:2 = fork [2] %result_31 {handshake.bb = 5 : ui32, handshake.name = "fork18"} : <>
    %91 = constant %90#0 {handshake.bb = 5 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %92 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %93 = constant %92 {handshake.bb = 5 : ui32, handshake.name = "constant17", value = 28 : i32} : <>, <i32>
    %94 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %95 = constant %94 {handshake.bb = 5 : ui32, handshake.name = "constant18", value = 1 : i32} : <>, <i32>
    %addressResult_33, %dataResult_34 = store[%89] %86#0 {handshake.bb = 5 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i10>, <i32>, <i10>, <i32>
    %96 = addi %88#1, %95 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i32>
    %97:2 = fork [2] %96 {handshake.bb = 5 : ui32, handshake.name = "fork19"} : <i32>
    %98 = cmpi ne, %97#1, %93 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %99:3 = fork [3] %98 {handshake.bb = 5 : ui32, handshake.name = "fork20"} : <i1>
    %trueResult_35, %falseResult_36 = cond_br %99#2, %97#0 {handshake.bb = 5 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    sink %falseResult_36 {handshake.name = "sink6"} : <i32>
    %trueResult_37, %falseResult_38 = cond_br %99#1, %90#1 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %trueResult_39, %falseResult_40 = cond_br %99#0, %86#1 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    sink %trueResult_39 {handshake.name = "sink7"} : <i32>
    %100 = merge %falseResult_40 {handshake.bb = 6 : ui32, handshake.name = "merge5"} : <i32>
    %result_41, %index_42 = control_merge [%falseResult_38]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_42 {handshake.name = "sink8"} : <i1>
    %101:3 = fork [3] %result_41 {handshake.bb = 6 : ui32, handshake.name = "fork21"} : <>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %100, %memEnd_2, %memEnd_0, %memEnd, %0#1 : <i32>, <>, <>, <>, <>
  }
}

