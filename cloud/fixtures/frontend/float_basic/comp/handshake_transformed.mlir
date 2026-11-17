module {
  handshake.func @float_basic(%arg0: memref<900xf32>, %arg1: memref<900xf32>, %arg2: memref<30xf32>, %arg3: memref<30xf32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "y", "x", "A_start", "B_start", "y_start", "x_start", "start"], resNames = ["A_end", "B_end", "y_end", "x_end", "end"]} {
    %0:3 = fork [3] %arg8 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg3 : memref<30xf32>] %arg7 (%addressResult) %179#3 {connectedBlocks = [2 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i5>) -> !handshake.channel<f32>
    %memEnd_0 = mem_controller[%arg2 : memref<30xf32>] %arg6 (%170, %addressResult_47, %dataResult_48) %179#2 {connectedBlocks = [6 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i32>, !handshake.channel<i5>, !handshake.channel<f32>) -> ()
    %outputs_1:2, %memEnd_2 = mem_controller[%arg1 : memref<900xf32>] %arg5 (%addressResult_9, %addressResult_29) %179#1 {connectedBlocks = [2 : i32, 4 : i32], handshake.name = "mem_controller6"} :    (!handshake.channel<i10>, !handshake.channel<i10>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %outputs_3:2, %memEnd_4 = mem_controller[%arg0 : memref<900xf32>] %arg4 (%addressResult_7, %addressResult_25) %179#0 {connectedBlocks = [2 : i32, 3 : i32], handshake.name = "mem_controller7"} :    (!handshake.channel<i10>, !handshake.channel<i10>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui10"} : <i1> to <i5>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <>
    %5 = mux %index [%3, %trueResult_49] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %6:3 = fork [3] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %result, %index = control_merge [%4, %trueResult_51]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %8 = constant %7#2 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 0.000000e+00 : f32} : <>, <f32>
    %9 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <f32>
    %10 = constant %7#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %11 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i1>
    %12 = extui %11 {handshake.bb = 2 : ui32, handshake.name = "extui11"} : <i1> to <i5>
    %13 = br %6#2 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i5>
    %14 = br %6#0 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i5>
    %15 = br %6#1 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <i5>
    %16 = br %7#1 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <>
    %17 = mux %31#4 [%9, %trueResult_33] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %18 = mux %31#3 [%12, %trueResult_35] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i5>, <i5>] to <i5>
    %19:4 = fork [4] %18 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i5>
    %20 = extui %19#0 {handshake.bb = 2 : ui32, handshake.name = "extui12"} : <i5> to <i10>
    %21 = extui %19#1 {handshake.bb = 2 : ui32, handshake.name = "extui13"} : <i5> to <i10>
    %22 = mux %31#2 [%13, %trueResult_37] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i5>, <i5>] to <i5>
    %23 = mux %31#0 [%14, %trueResult_39] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i5>, <i5>] to <i5>
    %24:2 = fork [2] %23 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i5>
    %25 = extui %24#1 {handshake.bb = 2 : ui32, handshake.name = "extui14"} : <i5> to <i64>
    %26:4 = fork [4] %25 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i64>
    %27 = mux %31#1 [%15, %trueResult_41] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i5>, <i5>] to <i5>
    %28:2 = fork [2] %27 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i5>
    %29 = extui %28#1 {handshake.bb = 2 : ui32, handshake.name = "extui15"} : <i5> to <i64>
    %30:4 = fork [4] %29 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i64>
    %result_5, %index_6 = control_merge [%16, %trueResult_43]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %31:5 = fork [5] %index_6 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %32 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %33 = constant %32 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %34:2 = fork [2] %33 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i64>
    %35 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %36 = constant %35 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 3 : i64} : <>, <i64>
    %37:2 = fork [2] %36 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i64>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %39 = constant %38 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 2 : i64} : <>, <i64>
    %40:2 = fork [2] %39 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i64>
    %41 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %42 = constant %41 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i64} : <>, <i64>
    %43:2 = fork [2] %42 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i64>
    %addressResult, %dataResult = load[%19#2] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i5>, <f32>, <i5>, <f32>
    %44 = shli %26#0, %43#1 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %45 = trunci %44 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i64> to <i10>
    %46 = shli %26#1, %40#1 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %47 = trunci %46 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i10>
    %48 = addi %45, %47 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i10>
    %49 = shli %26#2, %37#1 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %50 = trunci %49 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i64> to <i10>
    %51 = shli %26#3, %34#1 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %52 = trunci %51 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i64> to <i10>
    %53 = addi %50, %52 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i10>
    %54 = addi %48, %53 {handshake.bb = 2 : ui32, handshake.name = "addi8"} : <i10>
    %55 = addi %54, %20 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i10>
    %addressResult_7, %dataResult_8 = load[%55] %outputs_3#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <f32>, <i10>, <f32>
    %56 = shli %30#0, %43#0 {handshake.bb = 2 : ui32, handshake.name = "shli4"} : <i64>
    %57 = trunci %56 {handshake.bb = 2 : ui32, handshake.name = "trunci4"} : <i64> to <i10>
    %58 = shli %30#1, %40#0 {handshake.bb = 2 : ui32, handshake.name = "shli5"} : <i64>
    %59 = trunci %58 {handshake.bb = 2 : ui32, handshake.name = "trunci5"} : <i64> to <i10>
    %60 = addi %57, %59 {handshake.bb = 2 : ui32, handshake.name = "addi9"} : <i10>
    %61 = shli %30#2, %37#0 {handshake.bb = 2 : ui32, handshake.name = "shli6"} : <i64>
    %62 = trunci %61 {handshake.bb = 2 : ui32, handshake.name = "trunci6"} : <i64> to <i10>
    %63 = shli %30#3, %34#0 {handshake.bb = 2 : ui32, handshake.name = "shli7"} : <i64>
    %64 = trunci %63 {handshake.bb = 2 : ui32, handshake.name = "trunci7"} : <i64> to <i10>
    %65 = addi %62, %64 {handshake.bb = 2 : ui32, handshake.name = "addi10"} : <i10>
    %66 = addi %60, %65 {handshake.bb = 2 : ui32, handshake.name = "addi11"} : <i10>
    %67 = addi %66, %21 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i10>
    %addressResult_9, %dataResult_10 = load[%67] %outputs_1#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i10>, <f32>, <i10>, <f32>
    %68 = cmpf ugt, %dataResult_8, %dataResult_10 {handshake.bb = 2 : ui32, handshake.name = "cmpf0"} : <f32>
    %69:7 = fork [7] %68 {handshake.bb = 2 : ui32, handshake.name = "fork13"} : <i1>
    %trueResult, %falseResult = cond_br %69#2, %22 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i5>
    %trueResult_11, %falseResult_12 = cond_br %69#0, %24#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i5>
    %trueResult_13, %falseResult_14 = cond_br %69#1, %28#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    %trueResult_15, %falseResult_16 = cond_br %69#6, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %trueResult_17, %falseResult_18 = cond_br %69#3, %19#3 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i5>
    %trueResult_19, %falseResult_20 = cond_br %69#5, %dataResult {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <f32>
    %trueResult_21, %falseResult_22 = cond_br %69#4, %result_5 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %70 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i5>
    %71:2 = fork [2] %70 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i5>
    %72 = merge %falseResult_12 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i5>
    %73 = merge %falseResult_14 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i5>
    %74 = merge %falseResult_16 {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <f32>
    %75 = merge %falseResult_18 {handshake.bb = 3 : ui32, handshake.name = "merge4"} : <i5>
    %76:2 = fork [2] %75 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i5>
    %77 = extui %76#0 {handshake.bb = 3 : ui32, handshake.name = "extui16"} : <i5> to <i10>
    %78 = merge %falseResult_20 {handshake.bb = 3 : ui32, handshake.name = "merge5"} : <f32>
    %result_23, %index_24 = control_merge [%falseResult_22]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_24 {handshake.name = "sink0"} : <i1>
    %79 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %80 = constant %79 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 4 : i64} : <>, <i64>
    %81 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %82 = constant %81 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 3 : i64} : <>, <i64>
    %83 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %84 = constant %83 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 2 : i64} : <>, <i64>
    %85 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %86 = constant %85 {handshake.bb = 3 : ui32, handshake.name = "constant18", value = 1 : i64} : <>, <i64>
    %87 = extui %71#1 {handshake.bb = 3 : ui32, handshake.name = "extui5"} : <i5> to <i64>
    %88:4 = fork [4] %87 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i64>
    %89 = shli %88#3, %86 {handshake.bb = 3 : ui32, handshake.name = "shli8"} : <i64>
    %90 = trunci %89 {handshake.bb = 3 : ui32, handshake.name = "trunci8"} : <i64> to <i10>
    %91 = shli %88#2, %84 {handshake.bb = 3 : ui32, handshake.name = "shli9"} : <i64>
    %92 = trunci %91 {handshake.bb = 3 : ui32, handshake.name = "trunci9"} : <i64> to <i10>
    %93 = addi %90, %92 {handshake.bb = 3 : ui32, handshake.name = "addi12"} : <i10>
    %94 = shli %88#1, %82 {handshake.bb = 3 : ui32, handshake.name = "shli10"} : <i64>
    %95 = trunci %94 {handshake.bb = 3 : ui32, handshake.name = "trunci10"} : <i64> to <i10>
    %96 = shli %88#0, %80 {handshake.bb = 3 : ui32, handshake.name = "shli11"} : <i64>
    %97 = trunci %96 {handshake.bb = 3 : ui32, handshake.name = "trunci11"} : <i64> to <i10>
    %98 = addi %95, %97 {handshake.bb = 3 : ui32, handshake.name = "addi13"} : <i10>
    %99 = addi %93, %98 {handshake.bb = 3 : ui32, handshake.name = "addi14"} : <i10>
    %100 = addi %99, %77 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i10>
    %addressResult_25, %dataResult_26 = load[%100] %outputs_3#1 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i10>, <f32>, <i10>, <f32>
    %101 = divf %dataResult_26, %78 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "divf0"} : <f32>
    %102 = addf %74, %101 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf0"} : <f32>
    %103 = br %102 {handshake.bb = 3 : ui32, handshake.name = "br12"} : <f32>
    %104 = br %71#0 {handshake.bb = 3 : ui32, handshake.name = "br13"} : <i5>
    %105 = br %72 {handshake.bb = 3 : ui32, handshake.name = "br14"} : <i5>
    %106 = br %73 {handshake.bb = 3 : ui32, handshake.name = "br15"} : <i5>
    %107 = br %76#1 {handshake.bb = 3 : ui32, handshake.name = "br16"} : <i5>
    %108 = br %result_23 {handshake.bb = 3 : ui32, handshake.name = "br17"} : <>
    %109 = merge %trueResult {handshake.bb = 4 : ui32, handshake.name = "merge6"} : <i5>
    %110:2 = fork [2] %109 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <i5>
    %111 = merge %trueResult_11 {handshake.bb = 4 : ui32, handshake.name = "merge7"} : <i5>
    %112 = merge %trueResult_13 {handshake.bb = 4 : ui32, handshake.name = "merge8"} : <i5>
    %113 = merge %trueResult_15 {handshake.bb = 4 : ui32, handshake.name = "merge9"} : <f32>
    %114 = merge %trueResult_17 {handshake.bb = 4 : ui32, handshake.name = "merge10"} : <i5>
    %115:2 = fork [2] %114 {handshake.bb = 4 : ui32, handshake.name = "fork18"} : <i5>
    %116 = extui %115#0 {handshake.bb = 4 : ui32, handshake.name = "extui17"} : <i5> to <i10>
    %117 = merge %trueResult_19 {handshake.bb = 4 : ui32, handshake.name = "merge11"} : <f32>
    %result_27, %index_28 = control_merge [%trueResult_21]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_28 {handshake.name = "sink1"} : <i1>
    %118 = source {handshake.bb = 4 : ui32, handshake.name = "source8"} : <>
    %119 = constant %118 {handshake.bb = 4 : ui32, handshake.name = "constant19", value = 4 : i64} : <>, <i64>
    %120 = source {handshake.bb = 4 : ui32, handshake.name = "source9"} : <>
    %121 = constant %120 {handshake.bb = 4 : ui32, handshake.name = "constant20", value = 3 : i64} : <>, <i64>
    %122 = source {handshake.bb = 4 : ui32, handshake.name = "source10"} : <>
    %123 = constant %122 {handshake.bb = 4 : ui32, handshake.name = "constant21", value = 2 : i64} : <>, <i64>
    %124 = source {handshake.bb = 4 : ui32, handshake.name = "source11"} : <>
    %125 = constant %124 {handshake.bb = 4 : ui32, handshake.name = "constant22", value = 1 : i64} : <>, <i64>
    %126 = extui %110#1 {handshake.bb = 4 : ui32, handshake.name = "extui7"} : <i5> to <i64>
    %127:4 = fork [4] %126 {handshake.bb = 4 : ui32, handshake.name = "fork19"} : <i64>
    %128 = shli %127#3, %125 {handshake.bb = 4 : ui32, handshake.name = "shli12"} : <i64>
    %129 = trunci %128 {handshake.bb = 4 : ui32, handshake.name = "trunci12"} : <i64> to <i10>
    %130 = shli %127#2, %123 {handshake.bb = 4 : ui32, handshake.name = "shli13"} : <i64>
    %131 = trunci %130 {handshake.bb = 4 : ui32, handshake.name = "trunci13"} : <i64> to <i10>
    %132 = addi %129, %131 {handshake.bb = 4 : ui32, handshake.name = "addi15"} : <i10>
    %133 = shli %127#1, %121 {handshake.bb = 4 : ui32, handshake.name = "shli14"} : <i64>
    %134 = trunci %133 {handshake.bb = 4 : ui32, handshake.name = "trunci14"} : <i64> to <i10>
    %135 = shli %127#0, %119 {handshake.bb = 4 : ui32, handshake.name = "shli15"} : <i64>
    %136 = trunci %135 {handshake.bb = 4 : ui32, handshake.name = "trunci15"} : <i64> to <i10>
    %137 = addi %134, %136 {handshake.bb = 4 : ui32, handshake.name = "addi16"} : <i10>
    %138 = addi %132, %137 {handshake.bb = 4 : ui32, handshake.name = "addi17"} : <i10>
    %139 = addi %138, %116 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i10>
    %addressResult_29, %dataResult_30 = load[%139] %outputs_1#1 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : <i10>, <f32>, <i10>, <f32>
    %140 = mulf %dataResult_30, %117 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "mulf0"} : <f32>
    %141 = subf %113, %140 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "subf0"} : <f32>
    %142 = br %141 {handshake.bb = 4 : ui32, handshake.name = "br18"} : <f32>
    %143 = br %110#0 {handshake.bb = 4 : ui32, handshake.name = "br19"} : <i5>
    %144 = br %111 {handshake.bb = 4 : ui32, handshake.name = "br20"} : <i5>
    %145 = br %112 {handshake.bb = 4 : ui32, handshake.name = "br21"} : <i5>
    %146 = br %115#1 {handshake.bb = 4 : ui32, handshake.name = "br22"} : <i5>
    %147 = br %result_27 {handshake.bb = 4 : ui32, handshake.name = "br23"} : <>
    %148 = mux %155#4 [%103, %142] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<f32>, <f32>] to <f32>
    %149 = mux %155#2 [%104, %143] {handshake.bb = 5 : ui32, handshake.name = "mux7"} : <i1>, [<i5>, <i5>] to <i5>
    %150 = mux %155#0 [%105, %144] {handshake.bb = 5 : ui32, handshake.name = "mux8"} : <i1>, [<i5>, <i5>] to <i5>
    %151 = mux %155#1 [%106, %145] {handshake.bb = 5 : ui32, handshake.name = "mux9"} : <i1>, [<i5>, <i5>] to <i5>
    %152 = mux %155#3 [%107, %146] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<i5>, <i5>] to <i5>
    %153 = extui %152 {handshake.bb = 5 : ui32, handshake.name = "extui18"} : <i5> to <i6>
    %154 = constant %157 {handshake.bb = 5 : ui32, handshake.name = "constant5", value = 1 : i6} : <>, <i6>
    %result_31, %index_32 = control_merge [%108, %147]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %155:5 = fork [5] %index_32 {handshake.bb = 5 : ui32, handshake.name = "fork20"} : <i1>
    %156 = source {handshake.bb = 5 : ui32, handshake.name = "source12"} : <>
    %157 = source {handshake.bb = 5 : ui32, handshake.name = "source13"} : <>
    %158 = addi %153, %154 {handshake.bb = 5 : ui32, handshake.name = "addi4"} : <i6>
    %159:2 = fork [2] %158 {handshake.bb = 5 : ui32, handshake.name = "fork21"} : <i6>
    %160 = trunci %159#0 {handshake.bb = 5 : ui32, handshake.name = "trunci16"} : <i6> to <i5>
    %161 = constant %156 {handshake.bb = 5 : ui32, handshake.name = "constant6", value = 30 : i6} : <>, <i6>
    %162 = cmpi ult, %159#1, %161 {handshake.bb = 5 : ui32, handshake.name = "cmpi0"} : <i6>
    %163:6 = fork [6] %162 {handshake.bb = 5 : ui32, handshake.name = "fork22"} : <i1>
    %trueResult_33, %falseResult_34 = cond_br %163#4, %148 {handshake.bb = 5 : ui32, handshake.name = "cond_br10"} : <i1>, <f32>
    %trueResult_35, %falseResult_36 = cond_br %163#0, %160 {handshake.bb = 5 : ui32, handshake.name = "cond_br11"} : <i1>, <i5>
    sink %falseResult_36 {handshake.name = "sink2"} : <i5>
    %trueResult_37, %falseResult_38 = cond_br %163#3, %149 {handshake.bb = 5 : ui32, handshake.name = "cond_br12"} : <i1>, <i5>
    %trueResult_39, %falseResult_40 = cond_br %163#1, %150 {handshake.bb = 5 : ui32, handshake.name = "cond_br13"} : <i1>, <i5>
    sink %falseResult_40 {handshake.name = "sink3"} : <i5>
    %trueResult_41, %falseResult_42 = cond_br %163#2, %151 {handshake.bb = 5 : ui32, handshake.name = "cond_br14"} : <i1>, <i5>
    sink %falseResult_42 {handshake.name = "sink4"} : <i5>
    %trueResult_43, %falseResult_44 = cond_br %163#5, %result_31 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %164 = merge %falseResult_34 {handshake.bb = 6 : ui32, handshake.name = "merge12"} : <f32>
    %165 = merge %falseResult_38 {handshake.bb = 6 : ui32, handshake.name = "merge13"} : <i5>
    %166:2 = fork [2] %165 {handshake.bb = 6 : ui32, handshake.name = "fork23"} : <i5>
    %167 = extui %166#1 {handshake.bb = 6 : ui32, handshake.name = "extui19"} : <i5> to <i6>
    %168 = constant %172 {handshake.bb = 6 : ui32, handshake.name = "constant7", value = 1 : i6} : <>, <i6>
    %result_45, %index_46 = control_merge [%falseResult_44]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_46 {handshake.name = "sink5"} : <i1>
    %169:2 = fork [2] %result_45 {handshake.bb = 6 : ui32, handshake.name = "fork24"} : <>
    %170 = constant %169#0 {handshake.bb = 6 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %171 = source {handshake.bb = 6 : ui32, handshake.name = "source14"} : <>
    %172 = source {handshake.bb = 6 : ui32, handshake.name = "source15"} : <>
    %addressResult_47, %dataResult_48 = store[%166#0] %164 {handshake.bb = 6 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store5"} : <i5>, <f32>, <i5>, <f32>
    %173 = addi %167, %168 {handshake.bb = 6 : ui32, handshake.name = "addi5"} : <i6>
    %174:2 = fork [2] %173 {handshake.bb = 6 : ui32, handshake.name = "fork25"} : <i6>
    %175 = trunci %174#0 {handshake.bb = 6 : ui32, handshake.name = "trunci17"} : <i6> to <i5>
    %176 = constant %171 {handshake.bb = 6 : ui32, handshake.name = "constant8", value = 30 : i6} : <>, <i6>
    %177 = cmpi ult, %174#1, %176 {handshake.bb = 6 : ui32, handshake.name = "cmpi1"} : <i6>
    %178:2 = fork [2] %177 {handshake.bb = 6 : ui32, handshake.name = "fork26"} : <i1>
    %trueResult_49, %falseResult_50 = cond_br %178#0, %175 {handshake.bb = 6 : ui32, handshake.name = "cond_br16"} : <i1>, <i5>
    sink %falseResult_50 {handshake.name = "sink6"} : <i5>
    %trueResult_51, %falseResult_52 = cond_br %178#1, %169#1 {handshake.bb = 6 : ui32, handshake.name = "cond_br17"} : <i1>, <>
    %result_53, %index_54 = control_merge [%falseResult_52]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    sink %index_54 {handshake.name = "sink7"} : <i1>
    %179:4 = fork [4] %result_53 {handshake.bb = 7 : ui32, handshake.name = "fork27"} : <>
    end {handshake.bb = 7 : ui32, handshake.name = "end0"} %memEnd_4, %memEnd_2, %memEnd_0, %memEnd, %0#1 : <>, <>, <>, <>, <>
  }
}

