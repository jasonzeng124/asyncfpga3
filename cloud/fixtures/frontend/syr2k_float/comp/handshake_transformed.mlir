module {
  handshake.func @syr2k_float(%arg0: memref<900xf32>, %arg1: memref<900xf32>, %arg2: memref<900xf32>, %arg3: !handshake.channel<f32>, %arg4: !handshake.channel<f32>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "C", "alpha", "beta", "A_start", "B_start", "C_start", "start"], resNames = ["A_end", "B_end", "C_end", "end"]} {
    %0:3 = fork [3] %arg8 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:3 = lsq[%arg2 : memref<900xf32>] (%arg7, %36#0, %addressResult, %addressResult_4, %dataResult_5, %111#0, %addressResult_32, %267#0, %addressResult_70, %dataResult_71, %308#2)  {groupSizes = [2 : i32, 1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i10>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %outputs:2, %memEnd = mem_controller[%arg1 : memref<900xf32>] %arg6 (%addressResult_38, %addressResult_40) %308#1 {connectedBlocks = [6 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>, !handshake.channel<i10>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %outputs_0:2, %memEnd_1 = mem_controller[%arg0 : memref<900xf32>] %arg5 (%addressResult_36, %addressResult_42) %308#0 {connectedBlocks = [6 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i10>, !handshake.channel<i10>) -> (!handshake.channel<f32>, !handshake.channel<f32>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui14"} : <i1> to <i4>
    %5 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <f32>
    %6 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <f32>
    %7 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br7"} : <>
    %8 = mux %12#0 [%4, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i4>, <i4>] to <i4>
    %9:2 = fork [2] %8 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i4>
    %10 = mux %12#1 [%5, %trueResult_20] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %11 = mux %12#2 [%6, %trueResult_22] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%7, %trueResult_24]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %12:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %13:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <>
    %14 = constant %13#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %15 = br %14 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i1>
    %16 = extui %15 {handshake.bb = 2 : ui32, handshake.name = "extui15"} : <i1> to <i4>
    %17 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <f32>
    %18 = br %11 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <f32>
    %19 = br %9#1 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <i4>
    %20 = br %9#0 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i4>
    %21 = br %13#1 {handshake.bb = 1 : ui32, handshake.name = "br13"} : <>
    %22 = mux %35#2 [%16, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i4>, <i4>] to <i4>
    %23:2 = fork [2] %22 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i4>
    %24 = extui %23#0 {handshake.bb = 2 : ui32, handshake.name = "extui16"} : <i4> to <i10>
    %25 = extui %23#1 {handshake.bb = 2 : ui32, handshake.name = "extui17"} : <i4> to <i5>
    %26 = constant %38 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 1 : i5} : <>, <i5>
    %27 = mux %35#3 [%17, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %28 = mux %35#4 [%18, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<f32>, <f32>] to <f32>
    %29:2 = fork [2] %28 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <f32>
    %30 = mux %35#1 [%19, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i4>, <i4>] to <i4>
    %31 = mux %35#0 [%20, %trueResult_12] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i4>, <i4>] to <i4>
    %32:2 = fork [2] %31 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i4>
    %33 = extui %32#1 {handshake.bb = 2 : ui32, handshake.name = "extui18"} : <i4> to <i64>
    %34:4 = fork [4] %33 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i64>
    %result_2, %index_3 = control_merge [%21, %trueResult_14]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %35:5 = fork [5] %index_3 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %36:2 = lazy_fork [2] %result_2 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork0"} : <>
    %37 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %39 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %40 = constant %39 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %41 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %42 = constant %41 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 3 : i64} : <>, <i64>
    %43 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %44 = constant %43 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 2 : i64} : <>, <i64>
    %45 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %46 = constant %45 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i64} : <>, <i64>
    %47 = shli %34#0, %46 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %48 = trunci %47 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i64> to <i10>
    %49 = shli %34#1, %44 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %50 = trunci %49 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i10>
    %51 = addi %48, %50 {handshake.bb = 2 : ui32, handshake.name = "addi12"} : <i10>
    %52 = shli %34#2, %42 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %53 = trunci %52 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i64> to <i10>
    %54 = shli %34#3, %40 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %55 = trunci %54 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i64> to <i10>
    %56 = addi %53, %55 {handshake.bb = 2 : ui32, handshake.name = "addi13"} : <i10>
    %57 = addi %51, %56 {handshake.bb = 2 : ui32, handshake.name = "addi14"} : <i10>
    %58 = addi %57, %24 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i10>
    %59:2 = fork [2] %58 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i10>
    %addressResult, %dataResult = load[%59#1] %1#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i10>, <f32>, <i10>, <f32>
    %60 = mulf %dataResult, %29#1 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %addressResult_4, %dataResult_5 = store[%59#0] %60 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : <i10>, <f32>, <i10>, <f32>
    %61 = addi %25, %26 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i5>
    %62:2 = fork [2] %61 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i5>
    %63 = trunci %62#0 {handshake.bb = 2 : ui32, handshake.name = "trunci4"} : <i5> to <i4>
    %64 = constant %37 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 10 : i5} : <>, <i5>
    %65 = cmpi ult, %62#1, %64 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i5>
    %66:6 = fork [6] %65 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult, %falseResult = cond_br %66#0, %63 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i4>
    sink %falseResult {handshake.name = "sink0"} : <i4>
    %trueResult_6, %falseResult_7 = cond_br %66#3, %27 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %trueResult_8, %falseResult_9 = cond_br %66#4, %29#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <f32>
    %trueResult_10, %falseResult_11 = cond_br %66#2, %30 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i4>
    %trueResult_12, %falseResult_13 = cond_br %66#1, %32#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i4>
    sink %falseResult_13 {handshake.name = "sink1"} : <i4>
    %trueResult_14, %falseResult_15 = cond_br %66#5, %36#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %67 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <f32>
    %68 = merge %falseResult_9 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <f32>
    %69 = merge %falseResult_11 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i4>
    %70 = extui %69 {handshake.bb = 3 : ui32, handshake.name = "extui19"} : <i4> to <i5>
    %71 = constant %74 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = 1 : i5} : <>, <i5>
    %result_16, %index_17 = control_merge [%falseResult_15]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_17 {handshake.name = "sink2"} : <i1>
    %72:2 = fork [2] %result_16 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <>
    %73 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %74 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %75 = addi %70, %71 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i5>
    %76:2 = fork [2] %75 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i5>
    %77 = trunci %76#0 {handshake.bb = 3 : ui32, handshake.name = "trunci5"} : <i5> to <i4>
    %78 = constant %73 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 10 : i5} : <>, <i5>
    %79 = cmpi ult, %76#1, %78 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i5>
    %80:5 = fork [5] %79 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i1>
    %trueResult_18, %falseResult_19 = cond_br %80#0, %77 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <i4>
    sink %falseResult_19 {handshake.name = "sink3"} : <i4>
    %trueResult_20, %falseResult_21 = cond_br %80#1, %67 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <f32>
    %trueResult_22, %falseResult_23 = cond_br %80#2, %68 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <f32>
    sink %falseResult_23 {handshake.name = "sink4"} : <f32>
    %trueResult_24, %falseResult_25 = cond_br %80#3, %72#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %81 = constant %72#0 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = false} : <>, <i1>
    %trueResult_26, %falseResult_27 = cond_br %80#4, %81 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <i1>
    sink %trueResult_26 {handshake.name = "sink5"} : <i1>
    %82 = extui %falseResult_27 {handshake.bb = 4 : ui32, handshake.name = "extui20"} : <i1> to <i4>
    %83 = mux %86#0 [%82, %trueResult_90] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i4>, <i4>] to <i4>
    %84:5 = fork [5] %83 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <i4>
    %85 = mux %86#1 [%falseResult_21, %trueResult_92] {handshake.bb = 4 : ui32, handshake.name = "mux9"} : <i1>, [<f32>, <f32>] to <f32>
    %result_28, %index_29 = control_merge [%falseResult_25, %trueResult_94]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %86:2 = fork [2] %index_29 {handshake.bb = 4 : ui32, handshake.name = "fork16"} : <i1>
    %87:2 = fork [2] %result_28 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <>
    %88 = constant %87#0 {handshake.bb = 4 : ui32, handshake.name = "constant38", value = false} : <>, <i1>
    %89 = br %88 {handshake.bb = 4 : ui32, handshake.name = "br14"} : <i1>
    %90 = extui %89 {handshake.bb = 5 : ui32, handshake.name = "extui21"} : <i1> to <i4>
    %91 = br %85 {handshake.bb = 4 : ui32, handshake.name = "br15"} : <f32>
    %92 = br %84#4 {handshake.bb = 4 : ui32, handshake.name = "br16"} : <i4>
    %93 = br %84#0 {handshake.bb = 4 : ui32, handshake.name = "br17"} : <i4>
    %94 = br %84#1 {handshake.bb = 4 : ui32, handshake.name = "br18"} : <i4>
    %95 = br %84#2 {handshake.bb = 4 : ui32, handshake.name = "br19"} : <i4>
    %96 = br %84#3 {handshake.bb = 4 : ui32, handshake.name = "br20"} : <i4>
    %97 = br %87#1 {handshake.bb = 4 : ui32, handshake.name = "br21"} : <>
    %98 = mux %110#5 [%90, %trueResult_72] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<i4>, <i4>] to <i4>
    %99:4 = fork [4] %98 {handshake.bb = 5 : ui32, handshake.name = "fork18"} : <i4>
    %100 = extui %99#0 {handshake.bb = 5 : ui32, handshake.name = "extui22"} : <i4> to <i10>
    %101 = mux %110#6 [%91, %trueResult_74] {handshake.bb = 5 : ui32, handshake.name = "mux11"} : <i1>, [<f32>, <f32>] to <f32>
    %102 = mux %110#4 [%92, %trueResult_76] {handshake.bb = 5 : ui32, handshake.name = "mux12"} : <i1>, [<i4>, <i4>] to <i4>
    %103 = mux %110#0 [%93, %trueResult_78] {handshake.bb = 5 : ui32, handshake.name = "mux13"} : <i1>, [<i4>, <i4>] to <i4>
    %104:2 = fork [2] %103 {handshake.bb = 5 : ui32, handshake.name = "fork19"} : <i4>
    %105 = extui %104#1 {handshake.bb = 5 : ui32, handshake.name = "extui23"} : <i4> to <i64>
    %106:4 = fork [4] %105 {handshake.bb = 5 : ui32, handshake.name = "fork20"} : <i64>
    %107 = mux %110#1 [%94, %trueResult_80] {handshake.bb = 5 : ui32, handshake.name = "mux14"} : <i1>, [<i4>, <i4>] to <i4>
    %108 = mux %110#2 [%95, %trueResult_82] {handshake.bb = 5 : ui32, handshake.name = "mux15"} : <i1>, [<i4>, <i4>] to <i4>
    %109 = mux %110#3 [%96, %trueResult_84] {handshake.bb = 5 : ui32, handshake.name = "mux16"} : <i1>, [<i4>, <i4>] to <i4>
    %result_30, %index_31 = control_merge [%97, %trueResult_86]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %110:7 = fork [7] %index_31 {handshake.bb = 5 : ui32, handshake.name = "fork21"} : <i1>
    %111:3 = lazy_fork [3] %result_30 {handshake.bb = 5 : ui32, handshake.name = "lazy_fork1"} : <>
    %112 = source {handshake.bb = 5 : ui32, handshake.name = "source8"} : <>
    %113 = constant %112 {handshake.bb = 5 : ui32, handshake.name = "constant20", value = 4 : i64} : <>, <i64>
    %114 = source {handshake.bb = 5 : ui32, handshake.name = "source9"} : <>
    %115 = constant %114 {handshake.bb = 5 : ui32, handshake.name = "constant21", value = 3 : i64} : <>, <i64>
    %116 = source {handshake.bb = 5 : ui32, handshake.name = "source10"} : <>
    %117 = constant %116 {handshake.bb = 5 : ui32, handshake.name = "constant22", value = 2 : i64} : <>, <i64>
    %118 = source {handshake.bb = 5 : ui32, handshake.name = "source11"} : <>
    %119 = constant %118 {handshake.bb = 5 : ui32, handshake.name = "constant23", value = 1 : i64} : <>, <i64>
    %120 = shli %106#0, %119 {handshake.bb = 5 : ui32, handshake.name = "shli4"} : <i64>
    %121 = trunci %120 {handshake.bb = 5 : ui32, handshake.name = "trunci6"} : <i64> to <i10>
    %122 = shli %106#1, %117 {handshake.bb = 5 : ui32, handshake.name = "shli5"} : <i64>
    %123 = trunci %122 {handshake.bb = 5 : ui32, handshake.name = "trunci7"} : <i64> to <i10>
    %124 = addi %121, %123 {handshake.bb = 5 : ui32, handshake.name = "addi15"} : <i10>
    %125 = shli %106#2, %115 {handshake.bb = 5 : ui32, handshake.name = "shli6"} : <i64>
    %126 = trunci %125 {handshake.bb = 5 : ui32, handshake.name = "trunci8"} : <i64> to <i10>
    %127 = shli %106#3, %113 {handshake.bb = 5 : ui32, handshake.name = "shli7"} : <i64>
    %128 = trunci %127 {handshake.bb = 5 : ui32, handshake.name = "trunci9"} : <i64> to <i10>
    %129 = addi %126, %128 {handshake.bb = 5 : ui32, handshake.name = "addi16"} : <i10>
    %130 = addi %124, %129 {handshake.bb = 5 : ui32, handshake.name = "addi17"} : <i10>
    %131 = addi %130, %100 {handshake.bb = 5 : ui32, handshake.name = "addi3"} : <i10>
    %addressResult_32, %dataResult_33 = load[%131] %1#1 {handshake.bb = 5 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load2"} : <i10>, <f32>, <i10>, <f32>
    %132 = br %dataResult_33 {handshake.bb = 5 : ui32, handshake.name = "br22"} : <f32>
    %133 = constant %111#2 {handshake.bb = 5 : ui32, handshake.name = "constant39", value = false} : <>, <i1>
    %134 = br %133 {handshake.bb = 5 : ui32, handshake.name = "br23"} : <i1>
    %135 = extui %134 {handshake.bb = 6 : ui32, handshake.name = "extui24"} : <i1> to <i4>
    %136 = br %101 {handshake.bb = 5 : ui32, handshake.name = "br24"} : <f32>
    %137 = br %102 {handshake.bb = 5 : ui32, handshake.name = "br25"} : <i4>
    %138 = br %104#0 {handshake.bb = 5 : ui32, handshake.name = "br26"} : <i4>
    %139 = br %107 {handshake.bb = 5 : ui32, handshake.name = "br27"} : <i4>
    %140 = br %108 {handshake.bb = 5 : ui32, handshake.name = "br28"} : <i4>
    %141 = br %109 {handshake.bb = 5 : ui32, handshake.name = "br29"} : <i4>
    %142 = br %99#3 {handshake.bb = 5 : ui32, handshake.name = "br30"} : <i4>
    %143 = br %99#1 {handshake.bb = 5 : ui32, handshake.name = "br31"} : <i4>
    %144 = br %99#2 {handshake.bb = 5 : ui32, handshake.name = "br32"} : <i4>
    %145 = br %111#1 {handshake.bb = 5 : ui32, handshake.name = "br33"} : <>
    %146 = mux %177#9 [%132, %trueResult_44] {handshake.bb = 6 : ui32, handshake.name = "mux17"} : <i1>, [<f32>, <f32>] to <f32>
    %147 = mux %177#8 [%135, %trueResult_46] {handshake.bb = 6 : ui32, handshake.name = "mux18"} : <i1>, [<i4>, <i4>] to <i4>
    %148:5 = fork [5] %147 {handshake.bb = 6 : ui32, handshake.name = "fork22"} : <i4>
    %149 = extui %148#0 {handshake.bb = 6 : ui32, handshake.name = "extui25"} : <i4> to <i10>
    %150 = extui %148#1 {handshake.bb = 6 : ui32, handshake.name = "extui26"} : <i4> to <i10>
    %151 = extui %148#2 {handshake.bb = 6 : ui32, handshake.name = "extui27"} : <i4> to <i10>
    %152 = extui %148#3 {handshake.bb = 6 : ui32, handshake.name = "extui28"} : <i4> to <i10>
    %153 = extui %148#4 {handshake.bb = 6 : ui32, handshake.name = "extui29"} : <i4> to <i5>
    %154 = constant %179 {handshake.bb = 6 : ui32, handshake.name = "constant40", value = 1 : i5} : <>, <i5>
    %155 = mux %177#10 [%136, %trueResult_48] {handshake.bb = 6 : ui32, handshake.name = "mux19"} : <i1>, [<f32>, <f32>] to <f32>
    %156:3 = fork [3] %155 {handshake.bb = 6 : ui32, handshake.name = "fork23"} : <f32>
    %157 = mux %177#4 [%137, %trueResult_50] {handshake.bb = 6 : ui32, handshake.name = "mux20"} : <i1>, [<i4>, <i4>] to <i4>
    %158 = mux %177#0 [%138, %trueResult_52] {handshake.bb = 6 : ui32, handshake.name = "mux21"} : <i1>, [<i4>, <i4>] to <i4>
    %159 = mux %177#1 [%139, %trueResult_54] {handshake.bb = 6 : ui32, handshake.name = "mux22"} : <i1>, [<i4>, <i4>] to <i4>
    %160:2 = fork [2] %159 {handshake.bb = 6 : ui32, handshake.name = "fork24"} : <i4>
    %161 = extui %160#1 {handshake.bb = 6 : ui32, handshake.name = "extui30"} : <i4> to <i64>
    %162:4 = fork [4] %161 {handshake.bb = 6 : ui32, handshake.name = "fork25"} : <i64>
    %163 = mux %177#2 [%140, %trueResult_56] {handshake.bb = 6 : ui32, handshake.name = "mux23"} : <i1>, [<i4>, <i4>] to <i4>
    %164:2 = fork [2] %163 {handshake.bb = 6 : ui32, handshake.name = "fork26"} : <i4>
    %165 = extui %164#1 {handshake.bb = 6 : ui32, handshake.name = "extui31"} : <i4> to <i64>
    %166:4 = fork [4] %165 {handshake.bb = 6 : ui32, handshake.name = "fork27"} : <i64>
    %167 = mux %177#3 [%141, %trueResult_58] {handshake.bb = 6 : ui32, handshake.name = "mux24"} : <i1>, [<i4>, <i4>] to <i4>
    %168 = mux %177#7 [%142, %trueResult_60] {handshake.bb = 6 : ui32, handshake.name = "mux25"} : <i1>, [<i4>, <i4>] to <i4>
    %169 = mux %177#5 [%143, %trueResult_62] {handshake.bb = 6 : ui32, handshake.name = "mux26"} : <i1>, [<i4>, <i4>] to <i4>
    %170:2 = fork [2] %169 {handshake.bb = 6 : ui32, handshake.name = "fork28"} : <i4>
    %171 = extui %170#1 {handshake.bb = 6 : ui32, handshake.name = "extui32"} : <i4> to <i64>
    %172:4 = fork [4] %171 {handshake.bb = 6 : ui32, handshake.name = "fork29"} : <i64>
    %173 = mux %177#6 [%144, %trueResult_64] {handshake.bb = 6 : ui32, handshake.name = "mux27"} : <i1>, [<i4>, <i4>] to <i4>
    %174:2 = fork [2] %173 {handshake.bb = 6 : ui32, handshake.name = "fork30"} : <i4>
    %175 = extui %174#1 {handshake.bb = 6 : ui32, handshake.name = "extui33"} : <i4> to <i64>
    %176:4 = fork [4] %175 {handshake.bb = 6 : ui32, handshake.name = "fork31"} : <i64>
    %result_34, %index_35 = control_merge [%145, %trueResult_66]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %177:11 = fork [11] %index_35 {handshake.bb = 6 : ui32, handshake.name = "fork32"} : <i1>
    %178 = source {handshake.bb = 6 : ui32, handshake.name = "source12"} : <>
    %179 = source {handshake.bb = 6 : ui32, handshake.name = "source13"} : <>
    %180 = source {handshake.bb = 6 : ui32, handshake.name = "source14"} : <>
    %181 = constant %180 {handshake.bb = 6 : ui32, handshake.name = "constant26", value = 4 : i64} : <>, <i64>
    %182:4 = fork [4] %181 {handshake.bb = 6 : ui32, handshake.name = "fork33"} : <i64>
    %183 = source {handshake.bb = 6 : ui32, handshake.name = "source15"} : <>
    %184 = constant %183 {handshake.bb = 6 : ui32, handshake.name = "constant27", value = 3 : i64} : <>, <i64>
    %185:4 = fork [4] %184 {handshake.bb = 6 : ui32, handshake.name = "fork34"} : <i64>
    %186 = source {handshake.bb = 6 : ui32, handshake.name = "source16"} : <>
    %187 = constant %186 {handshake.bb = 6 : ui32, handshake.name = "constant28", value = 2 : i64} : <>, <i64>
    %188:4 = fork [4] %187 {handshake.bb = 6 : ui32, handshake.name = "fork35"} : <i64>
    %189 = source {handshake.bb = 6 : ui32, handshake.name = "source17"} : <>
    %190 = constant %189 {handshake.bb = 6 : ui32, handshake.name = "constant29", value = 1 : i64} : <>, <i64>
    %191:4 = fork [4] %190 {handshake.bb = 6 : ui32, handshake.name = "fork36"} : <i64>
    %192 = shli %162#0, %191#3 {handshake.bb = 6 : ui32, handshake.name = "shli8"} : <i64>
    %193 = trunci %192 {handshake.bb = 6 : ui32, handshake.name = "trunci10"} : <i64> to <i10>
    %194 = shli %162#1, %188#3 {handshake.bb = 6 : ui32, handshake.name = "shli9"} : <i64>
    %195 = trunci %194 {handshake.bb = 6 : ui32, handshake.name = "trunci11"} : <i64> to <i10>
    %196 = addi %193, %195 {handshake.bb = 6 : ui32, handshake.name = "addi18"} : <i10>
    %197 = shli %162#2, %185#3 {handshake.bb = 6 : ui32, handshake.name = "shli10"} : <i64>
    %198 = trunci %197 {handshake.bb = 6 : ui32, handshake.name = "trunci12"} : <i64> to <i10>
    %199 = shli %162#3, %182#3 {handshake.bb = 6 : ui32, handshake.name = "shli11"} : <i64>
    %200 = trunci %199 {handshake.bb = 6 : ui32, handshake.name = "trunci13"} : <i64> to <i10>
    %201 = addi %198, %200 {handshake.bb = 6 : ui32, handshake.name = "addi19"} : <i10>
    %202 = addi %196, %201 {handshake.bb = 6 : ui32, handshake.name = "addi20"} : <i10>
    %203 = addi %202, %149 {handshake.bb = 6 : ui32, handshake.name = "addi4"} : <i10>
    %addressResult_36, %dataResult_37 = load[%203] %outputs_0#0 {handshake.bb = 6 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : <i10>, <f32>, <i10>, <f32>
    %204 = mulf %dataResult_37, %156#2 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "mulf1"} : <f32>
    %205 = shli %172#0, %191#2 {handshake.bb = 6 : ui32, handshake.name = "shli12"} : <i64>
    %206 = trunci %205 {handshake.bb = 6 : ui32, handshake.name = "trunci14"} : <i64> to <i10>
    %207 = shli %172#1, %188#2 {handshake.bb = 6 : ui32, handshake.name = "shli13"} : <i64>
    %208 = trunci %207 {handshake.bb = 6 : ui32, handshake.name = "trunci15"} : <i64> to <i10>
    %209 = addi %206, %208 {handshake.bb = 6 : ui32, handshake.name = "addi21"} : <i10>
    %210 = shli %172#2, %185#2 {handshake.bb = 6 : ui32, handshake.name = "shli14"} : <i64>
    %211 = trunci %210 {handshake.bb = 6 : ui32, handshake.name = "trunci16"} : <i64> to <i10>
    %212 = shli %172#3, %182#2 {handshake.bb = 6 : ui32, handshake.name = "shli15"} : <i64>
    %213 = trunci %212 {handshake.bb = 6 : ui32, handshake.name = "trunci17"} : <i64> to <i10>
    %214 = addi %211, %213 {handshake.bb = 6 : ui32, handshake.name = "addi22"} : <i10>
    %215 = addi %209, %214 {handshake.bb = 6 : ui32, handshake.name = "addi23"} : <i10>
    %216 = addi %215, %150 {handshake.bb = 6 : ui32, handshake.name = "addi5"} : <i10>
    %addressResult_38, %dataResult_39 = load[%216] %outputs#0 {handshake.bb = 6 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : <i10>, <f32>, <i10>, <f32>
    %217 = mulf %204, %dataResult_39 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "mulf2"} : <f32>
    %218 = addf %146, %217 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "addf0"} : <f32>
    %219 = shli %166#0, %191#1 {handshake.bb = 6 : ui32, handshake.name = "shli16"} : <i64>
    %220 = trunci %219 {handshake.bb = 6 : ui32, handshake.name = "trunci18"} : <i64> to <i10>
    %221 = shli %166#1, %188#1 {handshake.bb = 6 : ui32, handshake.name = "shli17"} : <i64>
    %222 = trunci %221 {handshake.bb = 6 : ui32, handshake.name = "trunci19"} : <i64> to <i10>
    %223 = addi %220, %222 {handshake.bb = 6 : ui32, handshake.name = "addi24"} : <i10>
    %224 = shli %166#2, %185#1 {handshake.bb = 6 : ui32, handshake.name = "shli18"} : <i64>
    %225 = trunci %224 {handshake.bb = 6 : ui32, handshake.name = "trunci20"} : <i64> to <i10>
    %226 = shli %166#3, %182#1 {handshake.bb = 6 : ui32, handshake.name = "shli19"} : <i64>
    %227 = trunci %226 {handshake.bb = 6 : ui32, handshake.name = "trunci21"} : <i64> to <i10>
    %228 = addi %225, %227 {handshake.bb = 6 : ui32, handshake.name = "addi25"} : <i10>
    %229 = addi %223, %228 {handshake.bb = 6 : ui32, handshake.name = "addi26"} : <i10>
    %230 = addi %229, %151 {handshake.bb = 6 : ui32, handshake.name = "addi6"} : <i10>
    %addressResult_40, %dataResult_41 = load[%230] %outputs#1 {handshake.bb = 6 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load5"} : <i10>, <f32>, <i10>, <f32>
    %231 = mulf %dataResult_41, %156#1 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "mulf3"} : <f32>
    %232 = shli %176#0, %191#0 {handshake.bb = 6 : ui32, handshake.name = "shli20"} : <i64>
    %233 = trunci %232 {handshake.bb = 6 : ui32, handshake.name = "trunci22"} : <i64> to <i10>
    %234 = shli %176#1, %188#0 {handshake.bb = 6 : ui32, handshake.name = "shli21"} : <i64>
    %235 = trunci %234 {handshake.bb = 6 : ui32, handshake.name = "trunci23"} : <i64> to <i10>
    %236 = addi %233, %235 {handshake.bb = 6 : ui32, handshake.name = "addi27"} : <i10>
    %237 = shli %176#2, %185#0 {handshake.bb = 6 : ui32, handshake.name = "shli22"} : <i64>
    %238 = trunci %237 {handshake.bb = 6 : ui32, handshake.name = "trunci24"} : <i64> to <i10>
    %239 = shli %176#3, %182#0 {handshake.bb = 6 : ui32, handshake.name = "shli23"} : <i64>
    %240 = trunci %239 {handshake.bb = 6 : ui32, handshake.name = "trunci25"} : <i64> to <i10>
    %241 = addi %238, %240 {handshake.bb = 6 : ui32, handshake.name = "addi28"} : <i10>
    %242 = addi %236, %241 {handshake.bb = 6 : ui32, handshake.name = "addi29"} : <i10>
    %243 = addi %242, %152 {handshake.bb = 6 : ui32, handshake.name = "addi7"} : <i10>
    %addressResult_42, %dataResult_43 = load[%243] %outputs_0#1 {handshake.bb = 6 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load6"} : <i10>, <f32>, <i10>, <f32>
    %244 = mulf %231, %dataResult_43 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "mulf4"} : <f32>
    %245 = addf %218, %244 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "addf1"} : <f32>
    %246 = addi %153, %154 {handshake.bb = 6 : ui32, handshake.name = "addi8"} : <i5>
    %247:2 = fork [2] %246 {handshake.bb = 6 : ui32, handshake.name = "fork37"} : <i5>
    %248 = trunci %247#0 {handshake.bb = 6 : ui32, handshake.name = "trunci26"} : <i5> to <i4>
    %249 = constant %178 {handshake.bb = 6 : ui32, handshake.name = "constant41", value = 10 : i5} : <>, <i5>
    %250 = cmpi ult, %247#1, %249 {handshake.bb = 6 : ui32, handshake.name = "cmpi2"} : <i5>
    %251:12 = fork [12] %250 {handshake.bb = 6 : ui32, handshake.name = "fork38"} : <i1>
    %trueResult_44, %falseResult_45 = cond_br %251#9, %245 {handshake.bb = 6 : ui32, handshake.name = "cond_br16"} : <i1>, <f32>
    %trueResult_46, %falseResult_47 = cond_br %251#0, %248 {handshake.bb = 6 : ui32, handshake.name = "cond_br17"} : <i1>, <i4>
    sink %falseResult_47 {handshake.name = "sink6"} : <i4>
    %trueResult_48, %falseResult_49 = cond_br %251#10, %156#0 {handshake.bb = 6 : ui32, handshake.name = "cond_br18"} : <i1>, <f32>
    %trueResult_50, %falseResult_51 = cond_br %251#5, %157 {handshake.bb = 6 : ui32, handshake.name = "cond_br19"} : <i1>, <i4>
    %trueResult_52, %falseResult_53 = cond_br %251#1, %158 {handshake.bb = 6 : ui32, handshake.name = "cond_br20"} : <i1>, <i4>
    %trueResult_54, %falseResult_55 = cond_br %251#2, %160#0 {handshake.bb = 6 : ui32, handshake.name = "cond_br21"} : <i1>, <i4>
    %trueResult_56, %falseResult_57 = cond_br %251#3, %164#0 {handshake.bb = 6 : ui32, handshake.name = "cond_br22"} : <i1>, <i4>
    %trueResult_58, %falseResult_59 = cond_br %251#4, %167 {handshake.bb = 6 : ui32, handshake.name = "cond_br23"} : <i1>, <i4>
    %trueResult_60, %falseResult_61 = cond_br %251#8, %168 {handshake.bb = 6 : ui32, handshake.name = "cond_br24"} : <i1>, <i4>
    %trueResult_62, %falseResult_63 = cond_br %251#6, %170#0 {handshake.bb = 6 : ui32, handshake.name = "cond_br25"} : <i1>, <i4>
    sink %falseResult_63 {handshake.name = "sink7"} : <i4>
    %trueResult_64, %falseResult_65 = cond_br %251#7, %174#0 {handshake.bb = 6 : ui32, handshake.name = "cond_br26"} : <i1>, <i4>
    sink %falseResult_65 {handshake.name = "sink8"} : <i4>
    %trueResult_66, %falseResult_67 = cond_br %251#11, %result_34 {handshake.bb = 6 : ui32, handshake.name = "cond_br27"} : <i1>, <>
    %252 = merge %falseResult_45 {handshake.bb = 7 : ui32, handshake.name = "merge3"} : <f32>
    %253 = merge %falseResult_49 {handshake.bb = 7 : ui32, handshake.name = "merge4"} : <f32>
    %254 = merge %falseResult_51 {handshake.bb = 7 : ui32, handshake.name = "merge5"} : <i4>
    %255 = merge %falseResult_53 {handshake.bb = 7 : ui32, handshake.name = "merge6"} : <i4>
    %256 = merge %falseResult_55 {handshake.bb = 7 : ui32, handshake.name = "merge7"} : <i4>
    %257 = merge %falseResult_57 {handshake.bb = 7 : ui32, handshake.name = "merge8"} : <i4>
    %258 = merge %falseResult_59 {handshake.bb = 7 : ui32, handshake.name = "merge9"} : <i4>
    %259:2 = fork [2] %258 {handshake.bb = 7 : ui32, handshake.name = "fork39"} : <i4>
    %260 = extui %259#1 {handshake.bb = 7 : ui32, handshake.name = "extui34"} : <i4> to <i64>
    %261:4 = fork [4] %260 {handshake.bb = 7 : ui32, handshake.name = "fork40"} : <i64>
    %262 = merge %falseResult_61 {handshake.bb = 7 : ui32, handshake.name = "merge10"} : <i4>
    %263:2 = fork [2] %262 {handshake.bb = 7 : ui32, handshake.name = "fork41"} : <i4>
    %264 = extui %263#0 {handshake.bb = 7 : ui32, handshake.name = "extui35"} : <i4> to <i10>
    %265 = extui %263#1 {handshake.bb = 7 : ui32, handshake.name = "extui36"} : <i4> to <i5>
    %266 = constant %269 {handshake.bb = 7 : ui32, handshake.name = "constant42", value = 1 : i5} : <>, <i5>
    %result_68, %index_69 = control_merge [%falseResult_67]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    sink %index_69 {handshake.name = "sink9"} : <i1>
    %267:2 = lazy_fork [2] %result_68 {handshake.bb = 7 : ui32, handshake.name = "lazy_fork2"} : <>
    %268 = source {handshake.bb = 7 : ui32, handshake.name = "source18"} : <>
    %269 = source {handshake.bb = 7 : ui32, handshake.name = "source19"} : <>
    %270 = source {handshake.bb = 7 : ui32, handshake.name = "source20"} : <>
    %271 = constant %270 {handshake.bb = 7 : ui32, handshake.name = "constant32", value = 4 : i64} : <>, <i64>
    %272 = source {handshake.bb = 7 : ui32, handshake.name = "source21"} : <>
    %273 = constant %272 {handshake.bb = 7 : ui32, handshake.name = "constant33", value = 3 : i64} : <>, <i64>
    %274 = source {handshake.bb = 7 : ui32, handshake.name = "source22"} : <>
    %275 = constant %274 {handshake.bb = 7 : ui32, handshake.name = "constant34", value = 2 : i64} : <>, <i64>
    %276 = source {handshake.bb = 7 : ui32, handshake.name = "source23"} : <>
    %277 = constant %276 {handshake.bb = 7 : ui32, handshake.name = "constant35", value = 1 : i64} : <>, <i64>
    %278 = shli %261#0, %277 {handshake.bb = 7 : ui32, handshake.name = "shli24"} : <i64>
    %279 = trunci %278 {handshake.bb = 7 : ui32, handshake.name = "trunci27"} : <i64> to <i10>
    %280 = shli %261#1, %275 {handshake.bb = 7 : ui32, handshake.name = "shli25"} : <i64>
    %281 = trunci %280 {handshake.bb = 7 : ui32, handshake.name = "trunci28"} : <i64> to <i10>
    %282 = addi %279, %281 {handshake.bb = 7 : ui32, handshake.name = "addi30"} : <i10>
    %283 = shli %261#2, %273 {handshake.bb = 7 : ui32, handshake.name = "shli26"} : <i64>
    %284 = trunci %283 {handshake.bb = 7 : ui32, handshake.name = "trunci29"} : <i64> to <i10>
    %285 = shli %261#3, %271 {handshake.bb = 7 : ui32, handshake.name = "shli27"} : <i64>
    %286 = trunci %285 {handshake.bb = 7 : ui32, handshake.name = "trunci30"} : <i64> to <i10>
    %287 = addi %284, %286 {handshake.bb = 7 : ui32, handshake.name = "addi31"} : <i10>
    %288 = addi %282, %287 {handshake.bb = 7 : ui32, handshake.name = "addi32"} : <i10>
    %289 = addi %288, %264 {handshake.bb = 7 : ui32, handshake.name = "addi9"} : <i10>
    %addressResult_70, %dataResult_71 = store[%289] %252 {handshake.bb = 7 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store7"} : <i10>, <f32>, <i10>, <f32>
    %290 = addi %265, %266 {handshake.bb = 7 : ui32, handshake.name = "addi10"} : <i5>
    %291:2 = fork [2] %290 {handshake.bb = 7 : ui32, handshake.name = "fork42"} : <i5>
    %292 = trunci %291#0 {handshake.bb = 7 : ui32, handshake.name = "trunci31"} : <i5> to <i4>
    %293 = constant %268 {handshake.bb = 7 : ui32, handshake.name = "constant43", value = 10 : i5} : <>, <i5>
    %294 = cmpi ult, %291#1, %293 {handshake.bb = 7 : ui32, handshake.name = "cmpi3"} : <i5>
    %295:8 = fork [8] %294 {handshake.bb = 7 : ui32, handshake.name = "fork43"} : <i1>
    %trueResult_72, %falseResult_73 = cond_br %295#0, %292 {handshake.bb = 7 : ui32, handshake.name = "cond_br28"} : <i1>, <i4>
    sink %falseResult_73 {handshake.name = "sink10"} : <i4>
    %trueResult_74, %falseResult_75 = cond_br %295#6, %253 {handshake.bb = 7 : ui32, handshake.name = "cond_br29"} : <i1>, <f32>
    %trueResult_76, %falseResult_77 = cond_br %295#5, %254 {handshake.bb = 7 : ui32, handshake.name = "cond_br30"} : <i1>, <i4>
    %trueResult_78, %falseResult_79 = cond_br %295#1, %255 {handshake.bb = 7 : ui32, handshake.name = "cond_br31"} : <i1>, <i4>
    sink %falseResult_79 {handshake.name = "sink11"} : <i4>
    %trueResult_80, %falseResult_81 = cond_br %295#2, %256 {handshake.bb = 7 : ui32, handshake.name = "cond_br32"} : <i1>, <i4>
    sink %falseResult_81 {handshake.name = "sink12"} : <i4>
    %trueResult_82, %falseResult_83 = cond_br %295#3, %257 {handshake.bb = 7 : ui32, handshake.name = "cond_br33"} : <i1>, <i4>
    sink %falseResult_83 {handshake.name = "sink13"} : <i4>
    %trueResult_84, %falseResult_85 = cond_br %295#4, %259#0 {handshake.bb = 7 : ui32, handshake.name = "cond_br34"} : <i1>, <i4>
    sink %falseResult_85 {handshake.name = "sink14"} : <i4>
    %trueResult_86, %falseResult_87 = cond_br %295#7, %267#1 {handshake.bb = 7 : ui32, handshake.name = "cond_br35"} : <i1>, <>
    %296 = merge %falseResult_75 {handshake.bb = 8 : ui32, handshake.name = "merge11"} : <f32>
    %297 = merge %falseResult_77 {handshake.bb = 8 : ui32, handshake.name = "merge12"} : <i4>
    %298 = extui %297 {handshake.bb = 8 : ui32, handshake.name = "extui37"} : <i4> to <i5>
    %299 = constant %301 {handshake.bb = 8 : ui32, handshake.name = "constant44", value = 1 : i5} : <>, <i5>
    %result_88, %index_89 = control_merge [%falseResult_87]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>] to <>, <i1>
    sink %index_89 {handshake.name = "sink15"} : <i1>
    %300 = source {handshake.bb = 8 : ui32, handshake.name = "source24"} : <>
    %301 = source {handshake.bb = 8 : ui32, handshake.name = "source25"} : <>
    %302 = addi %298, %299 {handshake.bb = 8 : ui32, handshake.name = "addi11"} : <i5>
    %303:2 = fork [2] %302 {handshake.bb = 8 : ui32, handshake.name = "fork44"} : <i5>
    %304 = trunci %303#0 {handshake.bb = 8 : ui32, handshake.name = "trunci32"} : <i5> to <i4>
    %305 = constant %300 {handshake.bb = 8 : ui32, handshake.name = "constant45", value = 10 : i5} : <>, <i5>
    %306 = cmpi ult, %303#1, %305 {handshake.bb = 8 : ui32, handshake.name = "cmpi4"} : <i5>
    %307:3 = fork [3] %306 {handshake.bb = 8 : ui32, handshake.name = "fork45"} : <i1>
    %trueResult_90, %falseResult_91 = cond_br %307#0, %304 {handshake.bb = 8 : ui32, handshake.name = "cond_br36"} : <i1>, <i4>
    sink %falseResult_91 {handshake.name = "sink16"} : <i4>
    %trueResult_92, %falseResult_93 = cond_br %307#1, %296 {handshake.bb = 8 : ui32, handshake.name = "cond_br37"} : <i1>, <f32>
    sink %falseResult_93 {handshake.name = "sink17"} : <f32>
    %trueResult_94, %falseResult_95 = cond_br %307#2, %result_88 {handshake.bb = 8 : ui32, handshake.name = "cond_br38"} : <i1>, <>
    %result_96, %index_97 = control_merge [%falseResult_95]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    sink %index_97 {handshake.name = "sink18"} : <i1>
    %308:3 = fork [3] %result_96 {handshake.bb = 9 : ui32, handshake.name = "fork46"} : <>
    end {handshake.bb = 9 : ui32, handshake.name = "end0"} %memEnd_1, %memEnd, %1#2, %0#1 : <>, <>, <>, <>
  }
}

