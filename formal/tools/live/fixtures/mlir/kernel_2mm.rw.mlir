module {
  handshake.func @kernel_2mm(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: memref<100xi32>, %arg3: memref<100xi32>, %arg4: memref<100xi32>, %arg5: memref<100xi32>, %arg6: memref<100xi32>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, %arg11: !handshake.control<>, %arg12: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["alpha", "beta", "tmp", "A", "B", "C", "D", "tmp_start", "A_start", "B_start", "C_start", "D_start", "start"], resNames = ["tmp_end", "A_end", "B_end", "C_end", "D_end", "end"]} {
    %0:3 = fork [3] %arg12 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg6 : memref<100xi32>] %arg11 (%addressResult_64, %261, %addressResult_94, %dataResult_95) %292#4 {connectedBlocks = [7 : i32, 9 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i7>, !handshake.channel<i32>, !handshake.channel<i7>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg5 : memref<100xi32>] %arg10 (%addressResult_70) %292#3 {connectedBlocks = [8 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i7>) -> !handshake.channel<i32>
    %outputs_2, %memEnd_3 = mem_controller[%arg4 : memref<100xi32>] %arg9 (%addressResult_10) %292#2 {connectedBlocks = [3 : i32], handshake.name = "mem_controller6"} :    (!handshake.channel<i7>) -> !handshake.channel<i32>
    %outputs_4, %memEnd_5 = mem_controller[%arg3 : memref<100xi32>] %arg8 (%addressResult) %292#1 {connectedBlocks = [3 : i32], handshake.name = "mem_controller7"} :    (!handshake.channel<i7>) -> !handshake.channel<i32>
    %1:2 = lsq[%arg2 : memref<100xi32>] (%arg7, %110#0, %addressResult_32, %dataResult_33, %215#0, %addressResult_68, %292#0)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i7>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui14"} : <i1> to <i4>
    %5 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <i32>
    %6 = br %arg1 {handshake.bb = 0 : ui32, handshake.name = "br7"} : <i32>
    %7 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br8"} : <>
    %8 = mux %12#0 [%4, %trueResult_50] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i4>, <i4>] to <i4>
    %9:3 = fork [3] %8 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i4>
    %10 = mux %12#1 [%5, %trueResult_52] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %11 = mux %12#2 [%6, %trueResult_54] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%7, %trueResult_56]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %13:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <>
    %14 = constant %13#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %15 = br %14 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i1>
    %16 = extui %15 {handshake.bb = 2 : ui32, handshake.name = "extui15"} : <i1> to <i4>
    %17 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <i32>
    %18 = br %11 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <i32>
    %19 = br %9#2 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i4>
    %20 = br %9#0 {handshake.bb = 1 : ui32, handshake.name = "br13"} : <i4>
    %21 = br %9#1 {handshake.bb = 1 : ui32, handshake.name = "br14"} : <i4>
    %22 = br %13#1 {handshake.bb = 1 : ui32, handshake.name = "br15"} : <>
    %23 = mux %30#3 [%16, %trueResult_34] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i4>, <i4>] to <i4>
    %24:2 = fork [2] %23 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i4>
    %25 = mux %30#4 [%17, %trueResult_36] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %26 = mux %30#5 [%18, %trueResult_38] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %27 = mux %30#2 [%19, %trueResult_40] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i4>, <i4>] to <i4>
    %28 = mux %30#0 [%20, %trueResult_42] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i4>, <i4>] to <i4>
    %29 = mux %30#1 [%21, %trueResult_44] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i4>, <i4>] to <i4>
    %result_6, %index_7 = control_merge [%22, %trueResult_46]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %30:6 = fork [6] %index_7 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i1>
    %31:2 = fork [2] %result_6 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <>
    %32 = constant %31#0 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %33 = br %32 {handshake.bb = 2 : ui32, handshake.name = "br16"} : <i1>
    %34:2 = fork [2] %33 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i1>
    %35 = extui %34#1 {handshake.bb = 2 : ui32, handshake.name = "extui16"} : <i1> to <i32>
    %36 = extui %34#0 {handshake.bb = 3 : ui32, handshake.name = "extui17"} : <i1> to <i4>
    %37 = br %25 {handshake.bb = 2 : ui32, handshake.name = "br17"} : <i32>
    %38 = br %26 {handshake.bb = 2 : ui32, handshake.name = "br18"} : <i32>
    %39 = br %27 {handshake.bb = 2 : ui32, handshake.name = "br19"} : <i4>
    %40 = br %28 {handshake.bb = 2 : ui32, handshake.name = "br20"} : <i4>
    %41 = br %29 {handshake.bb = 2 : ui32, handshake.name = "br21"} : <i4>
    %42 = br %24#1 {handshake.bb = 2 : ui32, handshake.name = "br22"} : <i4>
    %43 = br %24#0 {handshake.bb = 2 : ui32, handshake.name = "br23"} : <i4>
    %44 = br %31#1 {handshake.bb = 2 : ui32, handshake.name = "br24"} : <>
    %45 = mux %64#5 [%36, %trueResult] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i4>, <i4>] to <i4>
    %46:3 = fork [3] %45 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i4>
    %47 = extui %46#0 {handshake.bb = 3 : ui32, handshake.name = "extui18"} : <i4> to <i7>
    %48 = extui %46#1 {handshake.bb = 3 : ui32, handshake.name = "extui19"} : <i4> to <i5>
    %49 = constant %66 {handshake.bb = 3 : ui32, handshake.name = "constant33", value = 1 : i5} : <>, <i5>
    %50 = mux %64#6 [%35, %trueResult_12] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %51 = mux %64#7 [%37, %trueResult_14] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %52:2 = fork [2] %51 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i32>
    %53 = mux %64#8 [%38, %trueResult_16] {handshake.bb = 3 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %54 = mux %64#2 [%39, %trueResult_18] {handshake.bb = 3 : ui32, handshake.name = "mux13"} : <i1>, [<i4>, <i4>] to <i4>
    %55 = mux %64#0 [%40, %trueResult_20] {handshake.bb = 3 : ui32, handshake.name = "mux14"} : <i1>, [<i4>, <i4>] to <i4>
    %56:2 = fork [2] %55 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i4>
    %57 = extui %56#1 {handshake.bb = 3 : ui32, handshake.name = "extui20"} : <i4> to <i64>
    %58:2 = fork [2] %57 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i64>
    %59 = mux %64#1 [%41, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux15"} : <i1>, [<i4>, <i4>] to <i4>
    %60 = mux %64#4 [%42, %trueResult_24] {handshake.bb = 3 : ui32, handshake.name = "mux16"} : <i1>, [<i4>, <i4>] to <i4>
    %61 = mux %64#3 [%43, %trueResult_26] {handshake.bb = 3 : ui32, handshake.name = "mux17"} : <i1>, [<i4>, <i4>] to <i4>
    %62:2 = fork [2] %61 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i4>
    %63 = extui %62#0 {handshake.bb = 3 : ui32, handshake.name = "extui21"} : <i4> to <i7>
    %result_8, %index_9 = control_merge [%44, %trueResult_28]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %64:9 = fork [9] %index_9 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i1>
    %65 = source {handshake.bb = 3 : ui32, handshake.name = "source0"} : <>
    %66 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %67 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %68 = constant %67 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 3 : i64} : <>, <i64>
    %69:2 = fork [2] %68 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i64>
    %70 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %71 = constant %70 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 1 : i64} : <>, <i64>
    %72:2 = fork [2] %71 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i64>
    %73 = shli %58#0, %72#1 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i64>
    %74 = trunci %73 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i64> to <i7>
    %75 = shli %58#1, %69#1 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i64>
    %76 = trunci %75 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i64> to <i7>
    %77 = addi %74, %76 {handshake.bb = 3 : ui32, handshake.name = "addi15"} : <i7>
    %78 = addi %77, %47 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i7>
    %addressResult, %dataResult = load[%78] %outputs_4 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %79 = muli %dataResult, %52#1 {handshake.bb = 3 : ui32, handshake.name = "muli1"} : <i32>
    %80 = extui %46#2 {handshake.bb = 3 : ui32, handshake.name = "extui4"} : <i4> to <i64>
    %81:2 = fork [2] %80 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i64>
    %82 = shli %81#1, %72#0 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i64>
    %83 = trunci %82 {handshake.bb = 3 : ui32, handshake.name = "trunci2"} : <i64> to <i7>
    %84 = shli %81#0, %69#0 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i64>
    %85 = trunci %84 {handshake.bb = 3 : ui32, handshake.name = "trunci3"} : <i64> to <i7>
    %86 = addi %83, %85 {handshake.bb = 3 : ui32, handshake.name = "addi16"} : <i7>
    %87 = addi %86, %63 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i7>
    %addressResult_10, %dataResult_11 = load[%87] %outputs_2 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i7>, <i32>, <i7>, <i32>
    %88 = muli %79, %dataResult_11 {handshake.bb = 3 : ui32, handshake.name = "muli3"} : <i32>
    %89 = addi %50, %88 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %90 = addi %48, %49 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i5>
    %91:2 = fork [2] %90 {handshake.bb = 3 : ui32, handshake.name = "fork17"} : <i5>
    %92 = trunci %91#0 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i5> to <i4>
    %93 = constant %65 {handshake.bb = 3 : ui32, handshake.name = "constant34", value = 10 : i5} : <>, <i5>
    %94 = cmpi ult, %91#1, %93 {handshake.bb = 3 : ui32, handshake.name = "cmpi0"} : <i5>
    %95:10 = fork [10] %94 {handshake.bb = 3 : ui32, handshake.name = "fork18"} : <i1>
    %trueResult, %falseResult = cond_br %95#0, %92 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <i4>
    sink %falseResult {handshake.name = "sink0"} : <i4>
    %trueResult_12, %falseResult_13 = cond_br %95#6, %89 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %95#7, %52#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %95#8, %53 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %95#3, %54 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <i4>
    %trueResult_20, %falseResult_21 = cond_br %95#1, %56#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <i4>
    %trueResult_22, %falseResult_23 = cond_br %95#2, %59 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i4>
    %trueResult_24, %falseResult_25 = cond_br %95#5, %60 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i4>
    %trueResult_26, %falseResult_27 = cond_br %95#4, %62#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i4>
    sink %falseResult_27 {handshake.name = "sink1"} : <i4>
    %trueResult_28, %falseResult_29 = cond_br %95#9, %result_8 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %96 = merge %falseResult_13 {handshake.bb = 4 : ui32, handshake.name = "merge0"} : <i32>
    %97 = merge %falseResult_15 {handshake.bb = 4 : ui32, handshake.name = "merge1"} : <i32>
    %98 = merge %falseResult_17 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i32>
    %99 = merge %falseResult_19 {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <i4>
    %100 = merge %falseResult_21 {handshake.bb = 4 : ui32, handshake.name = "merge4"} : <i4>
    %101 = merge %falseResult_23 {handshake.bb = 4 : ui32, handshake.name = "merge5"} : <i4>
    %102:2 = fork [2] %101 {handshake.bb = 4 : ui32, handshake.name = "fork19"} : <i4>
    %103 = extui %102#1 {handshake.bb = 4 : ui32, handshake.name = "extui22"} : <i4> to <i64>
    %104:2 = fork [2] %103 {handshake.bb = 4 : ui32, handshake.name = "fork20"} : <i64>
    %105 = merge %falseResult_25 {handshake.bb = 4 : ui32, handshake.name = "merge6"} : <i4>
    %106:2 = fork [2] %105 {handshake.bb = 4 : ui32, handshake.name = "fork21"} : <i4>
    %107 = extui %106#0 {handshake.bb = 4 : ui32, handshake.name = "extui23"} : <i4> to <i7>
    %108 = extui %106#1 {handshake.bb = 4 : ui32, handshake.name = "extui24"} : <i4> to <i5>
    %109 = constant %112 {handshake.bb = 4 : ui32, handshake.name = "constant35", value = 1 : i5} : <>, <i5>
    %result_30, %index_31 = control_merge [%falseResult_29]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_31 {handshake.name = "sink2"} : <i1>
    %110:2 = lazy_fork [2] %result_30 {handshake.bb = 4 : ui32, handshake.name = "lazy_fork0"} : <>
    %111 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %112 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %113 = source {handshake.bb = 4 : ui32, handshake.name = "source6"} : <>
    %114 = constant %113 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 3 : i64} : <>, <i64>
    %115 = source {handshake.bb = 4 : ui32, handshake.name = "source7"} : <>
    %116 = constant %115 {handshake.bb = 4 : ui32, handshake.name = "constant15", value = 1 : i64} : <>, <i64>
    %117 = shli %104#0, %116 {handshake.bb = 4 : ui32, handshake.name = "shli4"} : <i64>
    %118 = trunci %117 {handshake.bb = 4 : ui32, handshake.name = "trunci5"} : <i64> to <i7>
    %119 = shli %104#1, %114 {handshake.bb = 4 : ui32, handshake.name = "shli5"} : <i64>
    %120 = trunci %119 {handshake.bb = 4 : ui32, handshake.name = "trunci6"} : <i64> to <i7>
    %121 = addi %118, %120 {handshake.bb = 4 : ui32, handshake.name = "addi17"} : <i7>
    %122 = addi %121, %107 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i7>
    %addressResult_32, %dataResult_33 = store[%122] %96 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : <i7>, <i32>, <i7>, <i32>
    %123 = addi %108, %109 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i5>
    %124:2 = fork [2] %123 {handshake.bb = 4 : ui32, handshake.name = "fork22"} : <i5>
    %125 = trunci %124#0 {handshake.bb = 4 : ui32, handshake.name = "trunci7"} : <i5> to <i4>
    %126 = constant %111 {handshake.bb = 4 : ui32, handshake.name = "constant36", value = 10 : i5} : <>, <i5>
    %127 = cmpi ult, %124#1, %126 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i5>
    %128:7 = fork [7] %127 {handshake.bb = 4 : ui32, handshake.name = "fork23"} : <i1>
    %trueResult_34, %falseResult_35 = cond_br %128#0, %125 {handshake.bb = 4 : ui32, handshake.name = "cond_br16"} : <i1>, <i4>
    sink %falseResult_35 {handshake.name = "sink3"} : <i4>
    %trueResult_36, %falseResult_37 = cond_br %128#4, %97 {handshake.bb = 4 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_38, %falseResult_39 = cond_br %128#5, %98 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_40, %falseResult_41 = cond_br %128#3, %99 {handshake.bb = 4 : ui32, handshake.name = "cond_br19"} : <i1>, <i4>
    %trueResult_42, %falseResult_43 = cond_br %128#1, %100 {handshake.bb = 4 : ui32, handshake.name = "cond_br20"} : <i1>, <i4>
    sink %falseResult_43 {handshake.name = "sink4"} : <i4>
    %trueResult_44, %falseResult_45 = cond_br %128#2, %102#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br21"} : <i1>, <i4>
    sink %falseResult_45 {handshake.name = "sink5"} : <i4>
    %trueResult_46, %falseResult_47 = cond_br %128#6, %110#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br22"} : <i1>, <>
    %129 = merge %falseResult_37 {handshake.bb = 5 : ui32, handshake.name = "merge7"} : <i32>
    %130 = merge %falseResult_39 {handshake.bb = 5 : ui32, handshake.name = "merge8"} : <i32>
    %131 = merge %falseResult_41 {handshake.bb = 5 : ui32, handshake.name = "merge9"} : <i4>
    %132 = extui %131 {handshake.bb = 5 : ui32, handshake.name = "extui25"} : <i4> to <i5>
    %133 = constant %136 {handshake.bb = 5 : ui32, handshake.name = "constant37", value = 1 : i5} : <>, <i5>
    %result_48, %index_49 = control_merge [%falseResult_47]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    sink %index_49 {handshake.name = "sink6"} : <i1>
    %134:2 = fork [2] %result_48 {handshake.bb = 5 : ui32, handshake.name = "fork24"} : <>
    %135 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %136 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %137 = addi %132, %133 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i5>
    %138:2 = fork [2] %137 {handshake.bb = 5 : ui32, handshake.name = "fork25"} : <i5>
    %139 = trunci %138#0 {handshake.bb = 5 : ui32, handshake.name = "trunci8"} : <i5> to <i4>
    %140 = constant %135 {handshake.bb = 5 : ui32, handshake.name = "constant38", value = 10 : i5} : <>, <i5>
    %141 = cmpi ult, %138#1, %140 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i5>
    %142:5 = fork [5] %141 {handshake.bb = 5 : ui32, handshake.name = "fork26"} : <i1>
    %trueResult_50, %falseResult_51 = cond_br %142#0, %139 {handshake.bb = 5 : ui32, handshake.name = "cond_br23"} : <i1>, <i4>
    sink %falseResult_51 {handshake.name = "sink7"} : <i4>
    %trueResult_52, %falseResult_53 = cond_br %142#1, %129 {handshake.bb = 5 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    sink %falseResult_53 {handshake.name = "sink8"} : <i32>
    %trueResult_54, %falseResult_55 = cond_br %142#2, %130 {handshake.bb = 5 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_56, %falseResult_57 = cond_br %142#3, %134#1 {handshake.bb = 5 : ui32, handshake.name = "cond_br26"} : <i1>, <>
    %143 = constant %134#0 {handshake.bb = 5 : ui32, handshake.name = "constant39", value = false} : <>, <i1>
    %trueResult_58, %falseResult_59 = cond_br %142#4, %143 {handshake.bb = 5 : ui32, handshake.name = "cond_br27"} : <i1>, <i1>
    sink %trueResult_58 {handshake.name = "sink9"} : <i1>
    %144 = extui %falseResult_59 {handshake.bb = 6 : ui32, handshake.name = "extui26"} : <i1> to <i4>
    %145 = mux %148#0 [%144, %trueResult_112] {handshake.bb = 6 : ui32, handshake.name = "mux18"} : <i1>, [<i4>, <i4>] to <i4>
    %146:4 = fork [4] %145 {handshake.bb = 6 : ui32, handshake.name = "fork27"} : <i4>
    %147 = mux %148#1 [%falseResult_55, %trueResult_114] {handshake.bb = 6 : ui32, handshake.name = "mux19"} : <i1>, [<i32>, <i32>] to <i32>
    %result_60, %index_61 = control_merge [%falseResult_57, %trueResult_116]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %148:2 = fork [2] %index_61 {handshake.bb = 6 : ui32, handshake.name = "fork28"} : <i1>
    %149:2 = fork [2] %result_60 {handshake.bb = 6 : ui32, handshake.name = "fork29"} : <>
    %150 = constant %149#0 {handshake.bb = 6 : ui32, handshake.name = "constant40", value = false} : <>, <i1>
    %151 = br %150 {handshake.bb = 6 : ui32, handshake.name = "br25"} : <i1>
    %152 = extui %151 {handshake.bb = 7 : ui32, handshake.name = "extui27"} : <i1> to <i4>
    %153 = br %147 {handshake.bb = 6 : ui32, handshake.name = "br26"} : <i32>
    %154 = br %146#3 {handshake.bb = 6 : ui32, handshake.name = "br27"} : <i4>
    %155 = br %146#0 {handshake.bb = 6 : ui32, handshake.name = "br28"} : <i4>
    %156 = br %146#1 {handshake.bb = 6 : ui32, handshake.name = "br29"} : <i4>
    %157 = br %146#2 {handshake.bb = 6 : ui32, handshake.name = "br30"} : <i4>
    %158 = br %149#1 {handshake.bb = 6 : ui32, handshake.name = "br31"} : <>
    %159 = mux %171#4 [%152, %trueResult_96] {handshake.bb = 7 : ui32, handshake.name = "mux20"} : <i1>, [<i4>, <i4>] to <i4>
    %160:3 = fork [3] %159 {handshake.bb = 7 : ui32, handshake.name = "fork30"} : <i4>
    %161 = extui %160#0 {handshake.bb = 7 : ui32, handshake.name = "extui28"} : <i4> to <i7>
    %162 = mux %171#5 [%153, %trueResult_98] {handshake.bb = 7 : ui32, handshake.name = "mux21"} : <i1>, [<i32>, <i32>] to <i32>
    %163:2 = fork [2] %162 {handshake.bb = 7 : ui32, handshake.name = "fork31"} : <i32>
    %164 = mux %171#3 [%154, %trueResult_100] {handshake.bb = 7 : ui32, handshake.name = "mux22"} : <i1>, [<i4>, <i4>] to <i4>
    %165 = mux %171#0 [%155, %trueResult_102] {handshake.bb = 7 : ui32, handshake.name = "mux23"} : <i1>, [<i4>, <i4>] to <i4>
    %166:2 = fork [2] %165 {handshake.bb = 7 : ui32, handshake.name = "fork32"} : <i4>
    %167 = extui %166#1 {handshake.bb = 7 : ui32, handshake.name = "extui29"} : <i4> to <i64>
    %168:2 = fork [2] %167 {handshake.bb = 7 : ui32, handshake.name = "fork33"} : <i64>
    %169 = mux %171#1 [%156, %trueResult_104] {handshake.bb = 7 : ui32, handshake.name = "mux24"} : <i1>, [<i4>, <i4>] to <i4>
    %170 = mux %171#2 [%157, %trueResult_106] {handshake.bb = 7 : ui32, handshake.name = "mux25"} : <i1>, [<i4>, <i4>] to <i4>
    %result_62, %index_63 = control_merge [%158, %trueResult_108]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %171:6 = fork [6] %index_63 {handshake.bb = 7 : ui32, handshake.name = "fork34"} : <i1>
    %172:2 = fork [2] %result_62 {handshake.bb = 7 : ui32, handshake.name = "fork35"} : <>
    %173 = source {handshake.bb = 7 : ui32, handshake.name = "source10"} : <>
    %174 = constant %173 {handshake.bb = 7 : ui32, handshake.name = "constant21", value = 3 : i64} : <>, <i64>
    %175 = source {handshake.bb = 7 : ui32, handshake.name = "source11"} : <>
    %176 = constant %175 {handshake.bb = 7 : ui32, handshake.name = "constant22", value = 1 : i64} : <>, <i64>
    %177 = shli %168#0, %176 {handshake.bb = 7 : ui32, handshake.name = "shli6"} : <i64>
    %178 = trunci %177 {handshake.bb = 7 : ui32, handshake.name = "trunci9"} : <i64> to <i7>
    %179 = shli %168#1, %174 {handshake.bb = 7 : ui32, handshake.name = "shli7"} : <i64>
    %180 = trunci %179 {handshake.bb = 7 : ui32, handshake.name = "trunci10"} : <i64> to <i7>
    %181 = addi %178, %180 {handshake.bb = 7 : ui32, handshake.name = "addi18"} : <i7>
    %182 = addi %181, %161 {handshake.bb = 7 : ui32, handshake.name = "addi7"} : <i7>
    %addressResult_64, %dataResult_65 = load[%182] %outputs {handshake.bb = 7 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i7>, <i32>, <i7>, <i32>
    %183 = muli %dataResult_65, %163#1 {handshake.bb = 7 : ui32, handshake.name = "muli6"} : <i32>
    %184 = constant %172#0 {handshake.bb = 7 : ui32, handshake.name = "constant41", value = false} : <>, <i1>
    %185 = br %184 {handshake.bb = 7 : ui32, handshake.name = "br32"} : <i1>
    %186 = extui %185 {handshake.bb = 8 : ui32, handshake.name = "extui30"} : <i1> to <i4>
    %187 = br %183 {handshake.bb = 7 : ui32, handshake.name = "br33"} : <i32>
    %188 = br %163#0 {handshake.bb = 7 : ui32, handshake.name = "br34"} : <i32>
    %189 = br %164 {handshake.bb = 7 : ui32, handshake.name = "br35"} : <i4>
    %190 = br %166#0 {handshake.bb = 7 : ui32, handshake.name = "br36"} : <i4>
    %191 = br %169 {handshake.bb = 7 : ui32, handshake.name = "br37"} : <i4>
    %192 = br %170 {handshake.bb = 7 : ui32, handshake.name = "br38"} : <i4>
    %193 = br %160#2 {handshake.bb = 7 : ui32, handshake.name = "br39"} : <i4>
    %194 = br %160#1 {handshake.bb = 7 : ui32, handshake.name = "br40"} : <i4>
    %195 = br %172#1 {handshake.bb = 7 : ui32, handshake.name = "br41"} : <>
    %196 = mux %214#6 [%186, %trueResult_72] {handshake.bb = 8 : ui32, handshake.name = "mux26"} : <i1>, [<i4>, <i4>] to <i4>
    %197:3 = fork [3] %196 {handshake.bb = 8 : ui32, handshake.name = "fork36"} : <i4>
    %198 = extui %197#0 {handshake.bb = 8 : ui32, handshake.name = "extui31"} : <i4> to <i7>
    %199 = extui %197#1 {handshake.bb = 8 : ui32, handshake.name = "extui32"} : <i4> to <i5>
    %200 = constant %217 {handshake.bb = 8 : ui32, handshake.name = "constant42", value = 1 : i5} : <>, <i5>
    %201 = mux %214#7 [%187, %trueResult_74] {handshake.bb = 8 : ui32, handshake.name = "mux27"} : <i1>, [<i32>, <i32>] to <i32>
    %202 = mux %214#8 [%188, %trueResult_76] {handshake.bb = 8 : ui32, handshake.name = "mux28"} : <i1>, [<i32>, <i32>] to <i32>
    %203 = mux %214#3 [%189, %trueResult_78] {handshake.bb = 8 : ui32, handshake.name = "mux29"} : <i1>, [<i4>, <i4>] to <i4>
    %204 = mux %214#0 [%190, %trueResult_80] {handshake.bb = 8 : ui32, handshake.name = "mux30"} : <i1>, [<i4>, <i4>] to <i4>
    %205 = mux %214#1 [%191, %trueResult_82] {handshake.bb = 8 : ui32, handshake.name = "mux31"} : <i1>, [<i4>, <i4>] to <i4>
    %206:2 = fork [2] %205 {handshake.bb = 8 : ui32, handshake.name = "fork37"} : <i4>
    %207 = extui %206#1 {handshake.bb = 8 : ui32, handshake.name = "extui33"} : <i4> to <i64>
    %208:2 = fork [2] %207 {handshake.bb = 8 : ui32, handshake.name = "fork38"} : <i64>
    %209 = mux %214#2 [%192, %trueResult_84] {handshake.bb = 8 : ui32, handshake.name = "mux32"} : <i1>, [<i4>, <i4>] to <i4>
    %210 = mux %214#5 [%193, %trueResult_86] {handshake.bb = 8 : ui32, handshake.name = "mux33"} : <i1>, [<i4>, <i4>] to <i4>
    %211 = mux %214#4 [%194, %trueResult_88] {handshake.bb = 8 : ui32, handshake.name = "mux34"} : <i1>, [<i4>, <i4>] to <i4>
    %212:2 = fork [2] %211 {handshake.bb = 8 : ui32, handshake.name = "fork39"} : <i4>
    %213 = extui %212#0 {handshake.bb = 8 : ui32, handshake.name = "extui34"} : <i4> to <i7>
    %result_66, %index_67 = control_merge [%195, %trueResult_90]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>] to <>, <i1>
    %214:9 = fork [9] %index_67 {handshake.bb = 8 : ui32, handshake.name = "fork40"} : <i1>
    %215:2 = fork [2] %result_66 {handshake.bb = 8 : ui32, handshake.name = "fork41"} : <>
    %216 = source {handshake.bb = 8 : ui32, handshake.name = "source12"} : <>
    %217 = source {handshake.bb = 8 : ui32, handshake.name = "source13"} : <>
    %218 = source {handshake.bb = 8 : ui32, handshake.name = "source14"} : <>
    %219 = constant %218 {handshake.bb = 8 : ui32, handshake.name = "constant25", value = 3 : i64} : <>, <i64>
    %220:2 = fork [2] %219 {handshake.bb = 8 : ui32, handshake.name = "fork42"} : <i64>
    %221 = source {handshake.bb = 8 : ui32, handshake.name = "source15"} : <>
    %222 = constant %221 {handshake.bb = 8 : ui32, handshake.name = "constant26", value = 1 : i64} : <>, <i64>
    %223:2 = fork [2] %222 {handshake.bb = 8 : ui32, handshake.name = "fork43"} : <i64>
    %224 = shli %208#0, %223#1 {handshake.bb = 8 : ui32, handshake.name = "shli8"} : <i64>
    %225 = trunci %224 {handshake.bb = 8 : ui32, handshake.name = "trunci11"} : <i64> to <i7>
    %226 = shli %208#1, %220#1 {handshake.bb = 8 : ui32, handshake.name = "shli9"} : <i64>
    %227 = trunci %226 {handshake.bb = 8 : ui32, handshake.name = "trunci12"} : <i64> to <i7>
    %228 = addi %225, %227 {handshake.bb = 8 : ui32, handshake.name = "addi19"} : <i7>
    %229 = addi %228, %198 {handshake.bb = 8 : ui32, handshake.name = "addi8"} : <i7>
    %addressResult_68, %dataResult_69 = load[%229] %1#0 {handshake.bb = 8 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load4"} : <i7>, <i32>, <i7>, <i32>
    %230 = extui %197#2 {handshake.bb = 8 : ui32, handshake.name = "extui12"} : <i4> to <i64>
    %231:2 = fork [2] %230 {handshake.bb = 8 : ui32, handshake.name = "fork44"} : <i64>
    %232 = shli %231#1, %223#0 {handshake.bb = 8 : ui32, handshake.name = "shli10"} : <i64>
    %233 = trunci %232 {handshake.bb = 8 : ui32, handshake.name = "trunci13"} : <i64> to <i7>
    %234 = shli %231#0, %220#0 {handshake.bb = 8 : ui32, handshake.name = "shli11"} : <i64>
    %235 = trunci %234 {handshake.bb = 8 : ui32, handshake.name = "trunci14"} : <i64> to <i7>
    %236 = addi %233, %235 {handshake.bb = 8 : ui32, handshake.name = "addi20"} : <i7>
    %237 = addi %236, %213 {handshake.bb = 8 : ui32, handshake.name = "addi9"} : <i7>
    %addressResult_70, %dataResult_71 = load[%237] %outputs_0 {handshake.bb = 8 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load5"} : <i7>, <i32>, <i7>, <i32>
    %238 = muli %dataResult_69, %dataResult_71 {handshake.bb = 8 : ui32, handshake.name = "muli9"} : <i32>
    %239 = addi %201, %238 {handshake.bb = 8 : ui32, handshake.name = "addi10"} : <i32>
    %240 = addi %199, %200 {handshake.bb = 8 : ui32, handshake.name = "addi11"} : <i5>
    %241:2 = fork [2] %240 {handshake.bb = 8 : ui32, handshake.name = "fork45"} : <i5>
    %242 = trunci %241#0 {handshake.bb = 8 : ui32, handshake.name = "trunci15"} : <i5> to <i4>
    %243 = constant %216 {handshake.bb = 8 : ui32, handshake.name = "constant43", value = 10 : i5} : <>, <i5>
    %244 = cmpi ult, %241#1, %243 {handshake.bb = 8 : ui32, handshake.name = "cmpi3"} : <i5>
    %245:10 = fork [10] %244 {handshake.bb = 8 : ui32, handshake.name = "fork46"} : <i1>
    %trueResult_72, %falseResult_73 = cond_br %245#0, %242 {handshake.bb = 8 : ui32, handshake.name = "cond_br28"} : <i1>, <i4>
    sink %falseResult_73 {handshake.name = "sink10"} : <i4>
    %trueResult_74, %falseResult_75 = cond_br %245#7, %239 {handshake.bb = 8 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %trueResult_76, %falseResult_77 = cond_br %245#8, %202 {handshake.bb = 8 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_78, %falseResult_79 = cond_br %245#4, %203 {handshake.bb = 8 : ui32, handshake.name = "cond_br31"} : <i1>, <i4>
    %trueResult_80, %falseResult_81 = cond_br %245#1, %204 {handshake.bb = 8 : ui32, handshake.name = "cond_br32"} : <i1>, <i4>
    %trueResult_82, %falseResult_83 = cond_br %245#2, %206#0 {handshake.bb = 8 : ui32, handshake.name = "cond_br33"} : <i1>, <i4>
    %trueResult_84, %falseResult_85 = cond_br %245#3, %209 {handshake.bb = 8 : ui32, handshake.name = "cond_br34"} : <i1>, <i4>
    %trueResult_86, %falseResult_87 = cond_br %245#6, %210 {handshake.bb = 8 : ui32, handshake.name = "cond_br35"} : <i1>, <i4>
    %trueResult_88, %falseResult_89 = cond_br %245#5, %212#1 {handshake.bb = 8 : ui32, handshake.name = "cond_br36"} : <i1>, <i4>
    sink %falseResult_89 {handshake.name = "sink11"} : <i4>
    %trueResult_90, %falseResult_91 = cond_br %245#9, %215#1 {handshake.bb = 8 : ui32, handshake.name = "cond_br37"} : <i1>, <>
    %246 = merge %falseResult_75 {handshake.bb = 9 : ui32, handshake.name = "merge10"} : <i32>
    %247 = merge %falseResult_77 {handshake.bb = 9 : ui32, handshake.name = "merge11"} : <i32>
    %248 = merge %falseResult_79 {handshake.bb = 9 : ui32, handshake.name = "merge12"} : <i4>
    %249 = merge %falseResult_81 {handshake.bb = 9 : ui32, handshake.name = "merge13"} : <i4>
    %250 = merge %falseResult_83 {handshake.bb = 9 : ui32, handshake.name = "merge14"} : <i4>
    %251 = merge %falseResult_85 {handshake.bb = 9 : ui32, handshake.name = "merge15"} : <i4>
    %252:2 = fork [2] %251 {handshake.bb = 9 : ui32, handshake.name = "fork47"} : <i4>
    %253 = extui %252#1 {handshake.bb = 9 : ui32, handshake.name = "extui35"} : <i4> to <i64>
    %254:2 = fork [2] %253 {handshake.bb = 9 : ui32, handshake.name = "fork48"} : <i64>
    %255 = merge %falseResult_87 {handshake.bb = 9 : ui32, handshake.name = "merge16"} : <i4>
    %256:2 = fork [2] %255 {handshake.bb = 9 : ui32, handshake.name = "fork49"} : <i4>
    %257 = extui %256#0 {handshake.bb = 9 : ui32, handshake.name = "extui36"} : <i4> to <i7>
    %258 = extui %256#1 {handshake.bb = 9 : ui32, handshake.name = "extui37"} : <i4> to <i5>
    %259 = constant %263 {handshake.bb = 9 : ui32, handshake.name = "constant44", value = 1 : i5} : <>, <i5>
    %result_92, %index_93 = control_merge [%falseResult_91]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    sink %index_93 {handshake.name = "sink12"} : <i1>
    %260:2 = fork [2] %result_92 {handshake.bb = 9 : ui32, handshake.name = "fork50"} : <>
    %261 = constant %260#0 {handshake.bb = 9 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %262 = source {handshake.bb = 9 : ui32, handshake.name = "source16"} : <>
    %263 = source {handshake.bb = 9 : ui32, handshake.name = "source17"} : <>
    %264 = source {handshake.bb = 9 : ui32, handshake.name = "source18"} : <>
    %265 = constant %264 {handshake.bb = 9 : ui32, handshake.name = "constant29", value = 3 : i64} : <>, <i64>
    %266 = source {handshake.bb = 9 : ui32, handshake.name = "source19"} : <>
    %267 = constant %266 {handshake.bb = 9 : ui32, handshake.name = "constant30", value = 1 : i64} : <>, <i64>
    %268 = shli %254#0, %267 {handshake.bb = 9 : ui32, handshake.name = "shli12"} : <i64>
    %269 = trunci %268 {handshake.bb = 9 : ui32, handshake.name = "trunci16"} : <i64> to <i7>
    %270 = shli %254#1, %265 {handshake.bb = 9 : ui32, handshake.name = "shli13"} : <i64>
    %271 = trunci %270 {handshake.bb = 9 : ui32, handshake.name = "trunci17"} : <i64> to <i7>
    %272 = addi %269, %271 {handshake.bb = 9 : ui32, handshake.name = "addi21"} : <i7>
    %273 = addi %272, %257 {handshake.bb = 9 : ui32, handshake.name = "addi12"} : <i7>
    %addressResult_94, %dataResult_95 = store[%273] %246 {handshake.bb = 9 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store6"} : <i7>, <i32>, <i7>, <i32>
    %274 = addi %258, %259 {handshake.bb = 9 : ui32, handshake.name = "addi13"} : <i5>
    %275:2 = fork [2] %274 {handshake.bb = 9 : ui32, handshake.name = "fork51"} : <i5>
    %276 = trunci %275#0 {handshake.bb = 9 : ui32, handshake.name = "trunci18"} : <i5> to <i4>
    %277 = constant %262 {handshake.bb = 9 : ui32, handshake.name = "constant45", value = 10 : i5} : <>, <i5>
    %278 = cmpi ult, %275#1, %277 {handshake.bb = 9 : ui32, handshake.name = "cmpi4"} : <i5>
    %279:7 = fork [7] %278 {handshake.bb = 9 : ui32, handshake.name = "fork52"} : <i1>
    %trueResult_96, %falseResult_97 = cond_br %279#0, %276 {handshake.bb = 9 : ui32, handshake.name = "cond_br38"} : <i1>, <i4>
    sink %falseResult_97 {handshake.name = "sink13"} : <i4>
    %trueResult_98, %falseResult_99 = cond_br %279#5, %247 {handshake.bb = 9 : ui32, handshake.name = "cond_br39"} : <i1>, <i32>
    %trueResult_100, %falseResult_101 = cond_br %279#4, %248 {handshake.bb = 9 : ui32, handshake.name = "cond_br40"} : <i1>, <i4>
    %trueResult_102, %falseResult_103 = cond_br %279#1, %249 {handshake.bb = 9 : ui32, handshake.name = "cond_br41"} : <i1>, <i4>
    sink %falseResult_103 {handshake.name = "sink14"} : <i4>
    %trueResult_104, %falseResult_105 = cond_br %279#2, %250 {handshake.bb = 9 : ui32, handshake.name = "cond_br42"} : <i1>, <i4>
    sink %falseResult_105 {handshake.name = "sink15"} : <i4>
    %trueResult_106, %falseResult_107 = cond_br %279#3, %252#0 {handshake.bb = 9 : ui32, handshake.name = "cond_br43"} : <i1>, <i4>
    sink %falseResult_107 {handshake.name = "sink16"} : <i4>
    %trueResult_108, %falseResult_109 = cond_br %279#6, %260#1 {handshake.bb = 9 : ui32, handshake.name = "cond_br44"} : <i1>, <>
    %280 = merge %falseResult_99 {handshake.bb = 10 : ui32, handshake.name = "merge17"} : <i32>
    %281 = merge %falseResult_101 {handshake.bb = 10 : ui32, handshake.name = "merge18"} : <i4>
    %282 = extui %281 {handshake.bb = 10 : ui32, handshake.name = "extui38"} : <i4> to <i5>
    %283 = constant %285 {handshake.bb = 10 : ui32, handshake.name = "constant46", value = 1 : i5} : <>, <i5>
    %result_110, %index_111 = control_merge [%falseResult_109]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>] to <>, <i1>
    sink %index_111 {handshake.name = "sink17"} : <i1>
    %284 = source {handshake.bb = 10 : ui32, handshake.name = "source20"} : <>
    %285 = source {handshake.bb = 10 : ui32, handshake.name = "source21"} : <>
    %286 = addi %282, %283 {handshake.bb = 10 : ui32, handshake.name = "addi14"} : <i5>
    %287:2 = fork [2] %286 {handshake.bb = 10 : ui32, handshake.name = "fork53"} : <i5>
    %288 = trunci %287#0 {handshake.bb = 10 : ui32, handshake.name = "trunci19"} : <i5> to <i4>
    %289 = constant %284 {handshake.bb = 10 : ui32, handshake.name = "constant47", value = 10 : i5} : <>, <i5>
    %290 = cmpi ult, %287#1, %289 {handshake.bb = 10 : ui32, handshake.name = "cmpi5"} : <i5>
    %291:3 = fork [3] %290 {handshake.bb = 10 : ui32, handshake.name = "fork54"} : <i1>
    %trueResult_112, %falseResult_113 = cond_br %291#0, %288 {handshake.bb = 10 : ui32, handshake.name = "cond_br45"} : <i1>, <i4>
    sink %falseResult_113 {handshake.name = "sink18"} : <i4>
    %trueResult_114, %falseResult_115 = cond_br %291#1, %280 {handshake.bb = 10 : ui32, handshake.name = "cond_br46"} : <i1>, <i32>
    sink %falseResult_115 {handshake.name = "sink19"} : <i32>
    %trueResult_116, %falseResult_117 = cond_br %291#2, %result_110 {handshake.bb = 10 : ui32, handshake.name = "cond_br47"} : <i1>, <>
    %result_118, %index_119 = control_merge [%falseResult_117]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>] to <>, <i1>
    sink %index_119 {handshake.name = "sink20"} : <i1>
    %292:5 = fork [5] %result_118 {handshake.bb = 11 : ui32, handshake.name = "fork55"} : <>
    end {handshake.bb = 11 : ui32, handshake.name = "end0"} %1#1, %memEnd_5, %memEnd_3, %memEnd_1, %memEnd, %0#1 : <>, <>, <>, <>, <>, <>
  }
}

