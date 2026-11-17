module {
  handshake.func @stencil_2d(%arg0: memref<900xi32>, %arg1: memref<10xi32>, %arg2: memref<900xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["orig", "filter", "sol", "orig_start", "filter_start", "sol_start", "start"], resNames = ["out0", "orig_end", "filter_end", "sol_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg2 : memref<900xi32>] %arg5 (%101, %addressResult_33, %dataResult_34) %111#2 {connectedBlocks = [5 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<10xi32>] %arg4 (%addressResult) %111#1 {connectedBlocks = [3 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i4>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<900xi32>] %arg3 (%addressResult_7) %111#0 {connectedBlocks = [3 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i5>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %5 = mux %index [%3, %trueResult_35] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %result, %index = control_merge [%4, %trueResult_37]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <>
    %7 = constant %6#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %8 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i1>
    %9:2 = fork [2] %8 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %10 = extui %9#1 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i1> to <i32>
    %11 = extui %9#0 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i1> to <i2>
    %12 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i5>
    %13 = br %6#1 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <>
    %14 = mux %22#1 [%11, %trueResult_23] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i2>, <i2>] to <i2>
    %15:2 = fork [2] %14 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i2>
    %16 = extui %15#1 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i2> to <i32>
    %17:6 = fork [6] %16 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i32>
    %18 = mux %22#2 [%10, %trueResult_25] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %19 = mux %22#0 [%12, %trueResult_27] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i5>, <i5>] to <i5>
    %20:2 = fork [2] %19 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i5>
    %21 = extui %20#1 {handshake.bb = 2 : ui32, handshake.name = "extui7"} : <i5> to <i32>
    %result_3, %index_4 = control_merge [%13, %trueResult_29]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %22:3 = fork [3] %index_4 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i1>
    %23:2 = fork [2] %result_3 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <>
    %24 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %25 = constant %24 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %26:2 = fork [2] %25 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %28 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 3 : i32} : <>, <i32>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %30 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i32} : <>, <i32>
    %31 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %32 = constant %31 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 2 : i32} : <>, <i32>
    %33 = shli %17#0, %26#1 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i32>
    %34 = addi %17#1, %33 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i32>
    %35 = shli %17#2, %26#0 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i32>
    %36 = shli %17#3, %32 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i32>
    %37 = addi %35, %36 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i32>
    %38 = shli %17#4, %28 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i32>
    %39 = shli %17#5, %30 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i32>
    %40 = addi %38, %39 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i32>
    %41 = addi %37, %40 {handshake.bb = 2 : ui32, handshake.name = "addi10"} : <i32>
    %42 = addi %41, %21 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %43 = constant %23#0 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %44 = br %43 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <i1>
    %45 = extui %44 {handshake.bb = 3 : ui32, handshake.name = "extui8"} : <i1> to <i2>
    %46 = br %18 {handshake.bb = 2 : ui32, handshake.name = "br9"} : <i32>
    %47 = br %20#0 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <i5>
    %48 = br %15#0 {handshake.bb = 2 : ui32, handshake.name = "br11"} : <i2>
    %49 = br %34 {handshake.bb = 2 : ui32, handshake.name = "br12"} : <i32>
    %50 = br %42 {handshake.bb = 2 : ui32, handshake.name = "br13"} : <i32>
    %51 = br %23#1 {handshake.bb = 2 : ui32, handshake.name = "br14"} : <>
    %52 = mux %67#2 [%45, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i2>, <i2>] to <i2>
    %53:3 = fork [3] %52 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i2>
    %54 = extui %53#0 {handshake.bb = 3 : ui32, handshake.name = "extui9"} : <i2> to <i4>
    %55 = extui %53#1 {handshake.bb = 3 : ui32, handshake.name = "extui10"} : <i2> to <i10>
    %56 = extui %53#2 {handshake.bb = 3 : ui32, handshake.name = "extui11"} : <i2> to <i3>
    %57 = constant %68 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 1 : i3} : <>, <i3>
    %58 = mux %67#3 [%46, %trueResult_9] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %59 = mux %67#0 [%47, %trueResult_11] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i5>, <i5>] to <i5>
    %60 = mux %67#1 [%48, %trueResult_13] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i2>, <i2>] to <i2>
    %61 = mux %67#4 [%49, %trueResult_15] {handshake.bb = 3 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %62:2 = fork [2] %61 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %63 = trunci %62#0 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i32> to <i4>
    %64 = mux %67#5 [%50, %trueResult_17] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %65:2 = fork [2] %64 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i32>
    %66 = trunci %65#0 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %result_5, %index_6 = control_merge [%51, %trueResult_19]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %67:6 = fork [6] %index_6 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i1>
    %68 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %69 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %70 = addi %63, %54 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i4>
    %addressResult, %dataResult = load[%70] %outputs {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i4>, <i32>, <i4>, <i32>
    %71 = addi %66, %55 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i10>
    %addressResult_7, %dataResult_8 = load[%71] %outputs_1 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %72 = muli %dataResult, %dataResult_8 {handshake.bb = 3 : ui32, handshake.name = "muli2"} : <i32>
    %73 = addi %58, %72 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %74 = addi %56, %57 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i3>
    %75:2 = fork [2] %74 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i3>
    %76 = trunci %75#0 {handshake.bb = 3 : ui32, handshake.name = "trunci2"} : <i3> to <i2>
    %77 = constant %69 {handshake.bb = 3 : ui32, handshake.name = "constant19", value = 3 : i3} : <>, <i3>
    %78 = cmpi ult, %75#1, %77 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i3>
    %79:7 = fork [7] %78 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i1>
    %trueResult, %falseResult = cond_br %79#0, %76 {handshake.bb = 3 : ui32, handshake.name = "cond_br3"} : <i1>, <i2>
    sink %falseResult {handshake.name = "sink0"} : <i2>
    %trueResult_9, %falseResult_10 = cond_br %79#3, %73 {handshake.bb = 3 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %79#1, %59 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    %trueResult_13, %falseResult_14 = cond_br %79#2, %60 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i2>
    %trueResult_15, %falseResult_16 = cond_br %79#4, %62#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_16 {handshake.name = "sink1"} : <i32>
    %trueResult_17, %falseResult_18 = cond_br %79#5, %65#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_18 {handshake.name = "sink2"} : <i32>
    %trueResult_19, %falseResult_20 = cond_br %79#6, %result_5 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %80 = merge %falseResult_10 {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i32>
    %81 = merge %falseResult_12 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <i5>
    %82 = merge %falseResult_14 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i2>
    %83 = extui %82 {handshake.bb = 4 : ui32, handshake.name = "extui12"} : <i2> to <i3>
    %84 = constant %85 {handshake.bb = 4 : ui32, handshake.name = "constant20", value = 1 : i3} : <>, <i3>
    %result_21, %index_22 = control_merge [%falseResult_20]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_22 {handshake.name = "sink3"} : <i1>
    %85 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %86 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %87 = addi %83, %84 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i3>
    %88:2 = fork [2] %87 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i3>
    %89 = trunci %88#0 {handshake.bb = 4 : ui32, handshake.name = "trunci3"} : <i3> to <i2>
    %90 = constant %86 {handshake.bb = 4 : ui32, handshake.name = "constant21", value = 3 : i3} : <>, <i3>
    %91 = cmpi ult, %88#1, %90 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i3>
    %92:4 = fork [4] %91 {handshake.bb = 4 : ui32, handshake.name = "fork16"} : <i1>
    %trueResult_23, %falseResult_24 = cond_br %92#0, %89 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <i2>
    sink %falseResult_24 {handshake.name = "sink4"} : <i2>
    %trueResult_25, %falseResult_26 = cond_br %92#2, %80 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_27, %falseResult_28 = cond_br %92#1, %81 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i5>
    %trueResult_29, %falseResult_30 = cond_br %92#3, %result_21 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %93 = merge %falseResult_26 {handshake.bb = 5 : ui32, handshake.name = "merge3"} : <i32>
    %94:2 = fork [2] %93 {handshake.bb = 5 : ui32, handshake.name = "fork17"} : <i32>
    %95 = merge %falseResult_28 {handshake.bb = 5 : ui32, handshake.name = "merge4"} : <i5>
    %96:2 = fork [2] %95 {handshake.bb = 5 : ui32, handshake.name = "fork18"} : <i5>
    %97 = extui %96#1 {handshake.bb = 5 : ui32, handshake.name = "extui13"} : <i5> to <i6>
    %98 = constant %103 {handshake.bb = 5 : ui32, handshake.name = "constant22", value = 1 : i6} : <>, <i6>
    %99 = extui %96#0 {handshake.bb = 5 : ui32, handshake.name = "extui14"} : <i5> to <i10>
    %result_31, %index_32 = control_merge [%falseResult_30]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_32 {handshake.name = "sink5"} : <i1>
    %100:2 = fork [2] %result_31 {handshake.bb = 5 : ui32, handshake.name = "fork19"} : <>
    %101 = constant %100#0 {handshake.bb = 5 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %102 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %103 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %addressResult_33, %dataResult_34 = store[%99] %94#0 {handshake.bb = 5 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i10>, <i32>, <i10>, <i32>
    %104 = addi %97, %98 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i6>
    %105:2 = fork [2] %104 {handshake.bb = 5 : ui32, handshake.name = "fork20"} : <i6>
    %106 = trunci %105#0 {handshake.bb = 5 : ui32, handshake.name = "trunci4"} : <i6> to <i5>
    %107 = constant %102 {handshake.bb = 5 : ui32, handshake.name = "constant23", value = 28 : i6} : <>, <i6>
    %108 = cmpi ult, %105#1, %107 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i6>
    %109:3 = fork [3] %108 {handshake.bb = 5 : ui32, handshake.name = "fork21"} : <i1>
    %trueResult_35, %falseResult_36 = cond_br %109#0, %106 {handshake.bb = 5 : ui32, handshake.name = "cond_br14"} : <i1>, <i5>
    sink %falseResult_36 {handshake.name = "sink6"} : <i5>
    %trueResult_37, %falseResult_38 = cond_br %109#1, %100#1 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %trueResult_39, %falseResult_40 = cond_br %109#2, %94#1 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    sink %trueResult_39 {handshake.name = "sink7"} : <i32>
    %110 = merge %falseResult_40 {handshake.bb = 6 : ui32, handshake.name = "merge5"} : <i32>
    %result_41, %index_42 = control_merge [%falseResult_38]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_42 {handshake.name = "sink8"} : <i1>
    %111:3 = fork [3] %result_41 {handshake.bb = 6 : ui32, handshake.name = "fork22"} : <>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %110, %memEnd_2, %memEnd_0, %memEnd, %0#1 : <i32>, <>, <>, <>, <>
  }
}

