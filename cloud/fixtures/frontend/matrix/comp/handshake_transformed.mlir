module {
  handshake.func @matrix(%arg0: memref<900xi32>, %arg1: memref<900xi32>, %arg2: memref<900xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["inA", "inB", "outC", "inA_start", "inB_start", "outC_start", "start"], resNames = ["inA_end", "inB_end", "outC_end", "end"]} {
    %0:3 = fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg2 : memref<900xi32>] %arg5 (%111, %addressResult_25, %dataResult_26) %151#2 {connectedBlocks = [4 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg1 : memref<900xi32>] %arg4 (%addressResult_7) %151#1 {connectedBlocks = [3 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg0 : memref<900xi32>] %arg3 (%addressResult) %151#0 {connectedBlocks = [3 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %3 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui6"} : <i1> to <i5>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %5 = mux %index [%3, %trueResult_39] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %6:3 = fork [3] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %result, %index = control_merge [%4, %trueResult_41]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %8 = constant %7#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %9 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i1>
    %10 = extui %9 {handshake.bb = 2 : ui32, handshake.name = "extui7"} : <i1> to <i5>
    %11 = br %6#2 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i5>
    %12 = br %6#0 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i5>
    %13 = br %6#1 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i5>
    %14 = br %7#1 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %15 = mux %20#3 [%10, %trueResult_27] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i5>, <i5>] to <i5>
    %16:2 = fork [2] %15 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i5>
    %17 = mux %20#2 [%11, %trueResult_29] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i5>, <i5>] to <i5>
    %18 = mux %20#0 [%12, %trueResult_31] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i5>, <i5>] to <i5>
    %19 = mux %20#1 [%13, %trueResult_33] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i5>, <i5>] to <i5>
    %result_3, %index_4 = control_merge [%14, %trueResult_35]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %20:4 = fork [4] %index_4 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i1>
    %21:2 = fork [2] %result_3 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <>
    %22 = constant %21#0 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %23 = br %22 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <i1>
    %24:2 = fork [2] %23 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i1>
    %25 = extui %24#1 {handshake.bb = 2 : ui32, handshake.name = "extui8"} : <i1> to <i32>
    %26 = extui %24#0 {handshake.bb = 3 : ui32, handshake.name = "extui9"} : <i1> to <i5>
    %27 = br %17 {handshake.bb = 2 : ui32, handshake.name = "br11"} : <i5>
    %28 = br %18 {handshake.bb = 2 : ui32, handshake.name = "br12"} : <i5>
    %29 = br %19 {handshake.bb = 2 : ui32, handshake.name = "br13"} : <i5>
    %30 = br %16#1 {handshake.bb = 2 : ui32, handshake.name = "br14"} : <i5>
    %31 = br %16#0 {handshake.bb = 2 : ui32, handshake.name = "br15"} : <i5>
    %32 = br %21#1 {handshake.bb = 2 : ui32, handshake.name = "br16"} : <>
    %33 = mux %49#5 [%26, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i5>, <i5>] to <i5>
    %34:3 = fork [3] %33 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i5>
    %35 = extui %34#0 {handshake.bb = 3 : ui32, handshake.name = "extui10"} : <i5> to <i10>
    %36 = extui %34#1 {handshake.bb = 3 : ui32, handshake.name = "extui11"} : <i5> to <i6>
    %37 = constant %51 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 1 : i6} : <>, <i6>
    %38 = mux %49#6 [%25, %trueResult_9] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %39 = mux %49#2 [%27, %trueResult_11] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i5>, <i5>] to <i5>
    %40 = mux %49#0 [%28, %trueResult_13] {handshake.bb = 3 : ui32, handshake.name = "mux8"} : <i1>, [<i5>, <i5>] to <i5>
    %41:2 = fork [2] %40 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i5>
    %42 = extui %41#1 {handshake.bb = 3 : ui32, handshake.name = "extui12"} : <i5> to <i64>
    %43:4 = fork [4] %42 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i64>
    %44 = mux %49#1 [%29, %trueResult_15] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i5>, <i5>] to <i5>
    %45 = mux %49#4 [%30, %trueResult_17] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i5>, <i5>] to <i5>
    %46 = mux %49#3 [%31, %trueResult_19] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i5>, <i5>] to <i5>
    %47:2 = fork [2] %46 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i5>
    %48 = extui %47#0 {handshake.bb = 3 : ui32, handshake.name = "extui13"} : <i5> to <i10>
    %result_5, %index_6 = control_merge [%32, %trueResult_21]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %49:7 = fork [7] %index_6 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i1>
    %50 = source {handshake.bb = 3 : ui32, handshake.name = "source0"} : <>
    %51 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %52 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %53 = constant %52 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 4 : i64} : <>, <i64>
    %54:2 = fork [2] %53 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i64>
    %55 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %56 = constant %55 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 3 : i64} : <>, <i64>
    %57:2 = fork [2] %56 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i64>
    %58 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %59 = constant %58 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = 2 : i64} : <>, <i64>
    %60:2 = fork [2] %59 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i64>
    %61 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %62 = constant %61 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 1 : i64} : <>, <i64>
    %63:2 = fork [2] %62 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i64>
    %64 = shli %43#0, %63#1 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i64>
    %65 = trunci %64 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i64> to <i10>
    %66 = shli %43#1, %60#1 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i64>
    %67 = trunci %66 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i64> to <i10>
    %68 = addi %65, %67 {handshake.bb = 3 : ui32, handshake.name = "addi7"} : <i10>
    %69 = shli %43#2, %57#1 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i64>
    %70 = trunci %69 {handshake.bb = 3 : ui32, handshake.name = "trunci2"} : <i64> to <i10>
    %71 = shli %43#3, %54#1 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i64>
    %72 = trunci %71 {handshake.bb = 3 : ui32, handshake.name = "trunci3"} : <i64> to <i10>
    %73 = addi %70, %72 {handshake.bb = 3 : ui32, handshake.name = "addi8"} : <i10>
    %74 = addi %68, %73 {handshake.bb = 3 : ui32, handshake.name = "addi9"} : <i10>
    %75 = addi %74, %35 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i10>
    %addressResult, %dataResult = load[%75] %outputs_1 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %76 = extui %34#2 {handshake.bb = 3 : ui32, handshake.name = "extui4"} : <i5> to <i64>
    %77:4 = fork [4] %76 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i64>
    %78 = shli %77#3, %63#0 {handshake.bb = 3 : ui32, handshake.name = "shli4"} : <i64>
    %79 = trunci %78 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i64> to <i10>
    %80 = shli %77#2, %60#0 {handshake.bb = 3 : ui32, handshake.name = "shli5"} : <i64>
    %81 = trunci %80 {handshake.bb = 3 : ui32, handshake.name = "trunci5"} : <i64> to <i10>
    %82 = addi %79, %81 {handshake.bb = 3 : ui32, handshake.name = "addi10"} : <i10>
    %83 = shli %77#1, %57#0 {handshake.bb = 3 : ui32, handshake.name = "shli6"} : <i64>
    %84 = trunci %83 {handshake.bb = 3 : ui32, handshake.name = "trunci6"} : <i64> to <i10>
    %85 = shli %77#0, %54#0 {handshake.bb = 3 : ui32, handshake.name = "shli7"} : <i64>
    %86 = trunci %85 {handshake.bb = 3 : ui32, handshake.name = "trunci7"} : <i64> to <i10>
    %87 = addi %84, %86 {handshake.bb = 3 : ui32, handshake.name = "addi11"} : <i10>
    %88 = addi %82, %87 {handshake.bb = 3 : ui32, handshake.name = "addi12"} : <i10>
    %89 = addi %88, %48 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i10>
    %addressResult_7, %dataResult_8 = load[%89] %outputs {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %90 = muli %dataResult, %dataResult_8 {handshake.bb = 3 : ui32, handshake.name = "muli2"} : <i32>
    %91 = addi %38, %90 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %92 = addi %36, %37 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i6>
    %93:2 = fork [2] %92 {handshake.bb = 3 : ui32, handshake.name = "fork17"} : <i6>
    %94 = trunci %93#0 {handshake.bb = 3 : ui32, handshake.name = "trunci8"} : <i6> to <i5>
    %95 = constant %50 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = 30 : i6} : <>, <i6>
    %96 = cmpi ult, %93#1, %95 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i6>
    %97:8 = fork [8] %96 {handshake.bb = 3 : ui32, handshake.name = "fork18"} : <i1>
    %trueResult, %falseResult = cond_br %97#0, %94 {handshake.bb = 3 : ui32, handshake.name = "cond_br3"} : <i1>, <i5>
    sink %falseResult {handshake.name = "sink0"} : <i5>
    %trueResult_9, %falseResult_10 = cond_br %97#6, %91 {handshake.bb = 3 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %97#3, %39 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    %trueResult_13, %falseResult_14 = cond_br %97#1, %41#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i5>
    %trueResult_15, %falseResult_16 = cond_br %97#2, %44 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i5>
    %trueResult_17, %falseResult_18 = cond_br %97#5, %45 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i5>
    %trueResult_19, %falseResult_20 = cond_br %97#4, %47#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i5>
    sink %falseResult_20 {handshake.name = "sink1"} : <i5>
    %trueResult_21, %falseResult_22 = cond_br %97#7, %result_5 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %98 = merge %falseResult_10 {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i32>
    %99 = merge %falseResult_12 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <i5>
    %100 = merge %falseResult_14 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i5>
    %101 = merge %falseResult_16 {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <i5>
    %102:2 = fork [2] %101 {handshake.bb = 4 : ui32, handshake.name = "fork19"} : <i5>
    %103 = extui %102#1 {handshake.bb = 4 : ui32, handshake.name = "extui14"} : <i5> to <i64>
    %104:4 = fork [4] %103 {handshake.bb = 4 : ui32, handshake.name = "fork20"} : <i64>
    %105 = merge %falseResult_18 {handshake.bb = 4 : ui32, handshake.name = "merge4"} : <i5>
    %106:2 = fork [2] %105 {handshake.bb = 4 : ui32, handshake.name = "fork21"} : <i5>
    %107 = extui %106#0 {handshake.bb = 4 : ui32, handshake.name = "extui15"} : <i5> to <i10>
    %108 = extui %106#1 {handshake.bb = 4 : ui32, handshake.name = "extui16"} : <i5> to <i6>
    %109 = constant %113 {handshake.bb = 4 : ui32, handshake.name = "constant24", value = 1 : i6} : <>, <i6>
    %result_23, %index_24 = control_merge [%falseResult_22]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_24 {handshake.name = "sink2"} : <i1>
    %110:2 = fork [2] %result_23 {handshake.bb = 4 : ui32, handshake.name = "fork22"} : <>
    %111 = constant %110#0 {handshake.bb = 4 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %112 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %113 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %114 = source {handshake.bb = 4 : ui32, handshake.name = "source8"} : <>
    %115 = constant %114 {handshake.bb = 4 : ui32, handshake.name = "constant18", value = 4 : i64} : <>, <i64>
    %116 = source {handshake.bb = 4 : ui32, handshake.name = "source9"} : <>
    %117 = constant %116 {handshake.bb = 4 : ui32, handshake.name = "constant19", value = 3 : i64} : <>, <i64>
    %118 = source {handshake.bb = 4 : ui32, handshake.name = "source10"} : <>
    %119 = constant %118 {handshake.bb = 4 : ui32, handshake.name = "constant20", value = 2 : i64} : <>, <i64>
    %120 = source {handshake.bb = 4 : ui32, handshake.name = "source11"} : <>
    %121 = constant %120 {handshake.bb = 4 : ui32, handshake.name = "constant21", value = 1 : i64} : <>, <i64>
    %122 = shli %104#0, %121 {handshake.bb = 4 : ui32, handshake.name = "shli8"} : <i64>
    %123 = trunci %122 {handshake.bb = 4 : ui32, handshake.name = "trunci9"} : <i64> to <i10>
    %124 = shli %104#1, %119 {handshake.bb = 4 : ui32, handshake.name = "shli9"} : <i64>
    %125 = trunci %124 {handshake.bb = 4 : ui32, handshake.name = "trunci10"} : <i64> to <i10>
    %126 = addi %123, %125 {handshake.bb = 4 : ui32, handshake.name = "addi13"} : <i10>
    %127 = shli %104#2, %117 {handshake.bb = 4 : ui32, handshake.name = "shli10"} : <i64>
    %128 = trunci %127 {handshake.bb = 4 : ui32, handshake.name = "trunci11"} : <i64> to <i10>
    %129 = shli %104#3, %115 {handshake.bb = 4 : ui32, handshake.name = "shli11"} : <i64>
    %130 = trunci %129 {handshake.bb = 4 : ui32, handshake.name = "trunci12"} : <i64> to <i10>
    %131 = addi %128, %130 {handshake.bb = 4 : ui32, handshake.name = "addi14"} : <i10>
    %132 = addi %126, %131 {handshake.bb = 4 : ui32, handshake.name = "addi15"} : <i10>
    %133 = addi %132, %107 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i10>
    %addressResult_25, %dataResult_26 = store[%133] %98 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i10>, <i32>, <i10>, <i32>
    %134 = addi %108, %109 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i6>
    %135:2 = fork [2] %134 {handshake.bb = 4 : ui32, handshake.name = "fork23"} : <i6>
    %136 = trunci %135#0 {handshake.bb = 4 : ui32, handshake.name = "trunci13"} : <i6> to <i5>
    %137 = constant %112 {handshake.bb = 4 : ui32, handshake.name = "constant25", value = 30 : i6} : <>, <i6>
    %138 = cmpi ult, %135#1, %137 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i6>
    %139:5 = fork [5] %138 {handshake.bb = 4 : ui32, handshake.name = "fork24"} : <i1>
    %trueResult_27, %falseResult_28 = cond_br %139#0, %136 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <i5>
    sink %falseResult_28 {handshake.name = "sink3"} : <i5>
    %trueResult_29, %falseResult_30 = cond_br %139#3, %99 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i5>
    %trueResult_31, %falseResult_32 = cond_br %139#1, %100 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <i5>
    sink %falseResult_32 {handshake.name = "sink4"} : <i5>
    %trueResult_33, %falseResult_34 = cond_br %139#2, %102#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i5>
    sink %falseResult_34 {handshake.name = "sink5"} : <i5>
    %trueResult_35, %falseResult_36 = cond_br %139#4, %110#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %140 = merge %falseResult_30 {handshake.bb = 5 : ui32, handshake.name = "merge5"} : <i5>
    %141 = extui %140 {handshake.bb = 5 : ui32, handshake.name = "extui17"} : <i5> to <i6>
    %142 = constant %144 {handshake.bb = 5 : ui32, handshake.name = "constant26", value = 1 : i6} : <>, <i6>
    %result_37, %index_38 = control_merge [%falseResult_36]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_38 {handshake.name = "sink6"} : <i1>
    %143 = source {handshake.bb = 5 : ui32, handshake.name = "source12"} : <>
    %144 = source {handshake.bb = 5 : ui32, handshake.name = "source13"} : <>
    %145 = addi %141, %142 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i6>
    %146:2 = fork [2] %145 {handshake.bb = 5 : ui32, handshake.name = "fork25"} : <i6>
    %147 = trunci %146#0 {handshake.bb = 5 : ui32, handshake.name = "trunci14"} : <i6> to <i5>
    %148 = constant %143 {handshake.bb = 5 : ui32, handshake.name = "constant27", value = 30 : i6} : <>, <i6>
    %149 = cmpi ult, %146#1, %148 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i6>
    %150:2 = fork [2] %149 {handshake.bb = 5 : ui32, handshake.name = "fork26"} : <i1>
    %trueResult_39, %falseResult_40 = cond_br %150#0, %147 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i5>
    sink %falseResult_40 {handshake.name = "sink7"} : <i5>
    %trueResult_41, %falseResult_42 = cond_br %150#1, %result_37 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <>
    %result_43, %index_44 = control_merge [%falseResult_42]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_44 {handshake.name = "sink8"} : <i1>
    %151:3 = fork [3] %result_43 {handshake.bb = 6 : ui32, handshake.name = "fork27"} : <>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %memEnd_2, %memEnd_0, %memEnd, %0#1 : <>, <>, <>, <>
  }
}

