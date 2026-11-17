module {
  handshake.func @test_internal_array(%arg0: memref<640xi32>, %arg1: memref<640xi32>, %arg2: memref<640xi32>, %arg3: memref<640xi32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "C", "result", "A_start", "B_start", "C_start", "result_start", "start"], resNames = ["A_end", "B_end", "C_end", "result_end", "end"]} {
    %0:4 = fork [4] %arg8 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg3 : memref<640xi32>] %arg7 (%102, %addressResult_37, %dataResult_38) %135#4 {connectedBlocks = [5 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i32>, !handshake.channel<i10>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg2 : memref<640xi32>] %arg6 (%addressResult_35) %135#3 {connectedBlocks = [5 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg1 : memref<640xi32>] %arg5 (%addressResult_7) %135#2 {connectedBlocks = [2 : i32], handshake.name = "mem_controller6"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %outputs_3, %memEnd_4 = mem_controller[%arg0 : memref<640xi32>] %arg4 (%addressResult) %135#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller7"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1:2 = lsq[%2 : memref<640xi32>] (%0#1, %36#0, %addressResult_9, %dataResult_10, %101#0, %addressResult_33, %135#0)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i10>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    sink %1#1 {handshake.name = "sink0"} : <>
    %2 = "handshake.ram"() {handshake.name = "ram0", initialValue = dense<0> : memref<640xi32>} : () -> memref<640xi32>
    %3 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %5 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui12"} : <i1> to <i5>
    %6 = br %0#3 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %7 = mux %index [%5, %trueResult_23] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %8:4 = fork [4] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %result, %index = control_merge [%6, %trueResult_25]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %10 = constant %9#0 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = false} : <>, <i1>
    %11 = br %10 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i1>
    %12 = extui %11 {handshake.bb = 2 : ui32, handshake.name = "extui13"} : <i1> to <i5>
    %13 = br %8#3 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i5>
    %14 = br %8#0 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i5>
    %15 = br %8#1 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i5>
    %16 = br %8#2 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i5>
    %17 = br %9#1 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <>
    %18 = mux %35#4 [%12, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i5>, <i5>] to <i5>
    %19:4 = fork [4] %18 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i5>
    %20 = extui %19#0 {handshake.bb = 2 : ui32, handshake.name = "extui14"} : <i5> to <i10>
    %21 = extui %19#1 {handshake.bb = 2 : ui32, handshake.name = "extui15"} : <i5> to <i10>
    %22 = extui %19#2 {handshake.bb = 2 : ui32, handshake.name = "extui16"} : <i5> to <i10>
    %23 = extui %19#3 {handshake.bb = 2 : ui32, handshake.name = "extui17"} : <i5> to <i6>
    %24 = constant %38 {handshake.bb = 2 : ui32, handshake.name = "constant18", value = 1 : i6} : <>, <i6>
    %25 = mux %35#3 [%13, %trueResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i5>, <i5>] to <i5>
    %26 = mux %35#0 [%14, %trueResult_13] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i5>, <i5>] to <i5>
    %27:2 = fork [2] %26 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i5>
    %28 = extui %27#1 {handshake.bb = 2 : ui32, handshake.name = "extui18"} : <i5> to <i64>
    %29 = mux %35#1 [%15, %trueResult_15] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i5>, <i5>] to <i5>
    %30:2 = fork [2] %29 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i5>
    %31 = extui %30#1 {handshake.bb = 2 : ui32, handshake.name = "extui19"} : <i5> to <i64>
    %32 = mux %35#2 [%16, %trueResult_17] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i5>, <i5>] to <i5>
    %33:2 = fork [2] %32 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i5>
    %34 = extui %33#1 {handshake.bb = 2 : ui32, handshake.name = "extui20"} : <i5> to <i64>
    %result_5, %index_6 = control_merge [%17, %trueResult_19]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %35:5 = fork [5] %index_6 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i1>
    %36:2 = lazy_fork [2] %result_5 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork0"} : <>
    %37 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %38 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %39 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %40 = constant %39 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 5 : i64} : <>, <i64>
    %41:3 = fork [3] %40 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i64>
    %42 = shli %28, %41#2 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %43 = trunci %42 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i64> to <i10>
    %44 = addi %43, %20 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i10>
    %addressResult, %dataResult = load[%44] %outputs_3 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %45 = shli %31, %41#1 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %46 = trunci %45 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i64> to <i10>
    %47 = addi %46, %21 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i10>
    %addressResult_7, %dataResult_8 = load[%47] %outputs_1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %48 = muli %dataResult, %dataResult_8 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %49 = shli %34, %41#0 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %50 = trunci %49 {handshake.bb = 2 : ui32, handshake.name = "trunci2"} : <i64> to <i10>
    %51 = addi %50, %22 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i10>
    %addressResult_9, %dataResult_10 = store[%51] %48 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i10>, <i32>, <i10>, <i32>
    %52 = addi %23, %24 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i6>
    %53:2 = fork [2] %52 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i6>
    %54 = trunci %53#0 {handshake.bb = 2 : ui32, handshake.name = "trunci3"} : <i6> to <i5>
    %55 = constant %37 {handshake.bb = 2 : ui32, handshake.name = "constant19", value = -32 : i6} : <>, <i6>
    %56 = cmpi ult, %53#1, %55 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i6>
    %57:6 = fork [6] %56 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <i1>
    %trueResult, %falseResult = cond_br %57#0, %54 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i5>
    sink %falseResult {handshake.name = "sink1"} : <i5>
    %trueResult_11, %falseResult_12 = cond_br %57#4, %25 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i5>
    %trueResult_13, %falseResult_14 = cond_br %57#1, %27#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i5>
    sink %falseResult_14 {handshake.name = "sink2"} : <i5>
    %trueResult_15, %falseResult_16 = cond_br %57#2, %30#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i5>
    sink %falseResult_16 {handshake.name = "sink3"} : <i5>
    %trueResult_17, %falseResult_18 = cond_br %57#3, %33#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i5>
    sink %falseResult_18 {handshake.name = "sink4"} : <i5>
    %trueResult_19, %falseResult_20 = cond_br %57#5, %36#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %58 = merge %falseResult_12 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i5>
    %59 = extui %58 {handshake.bb = 3 : ui32, handshake.name = "extui21"} : <i5> to <i6>
    %60 = constant %63 {handshake.bb = 3 : ui32, handshake.name = "constant20", value = 1 : i6} : <>, <i6>
    %result_21, %index_22 = control_merge [%falseResult_20]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_22 {handshake.name = "sink5"} : <i1>
    %61:2 = fork [2] %result_21 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <>
    %62 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %63 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %64 = addi %59, %60 {handshake.bb = 3 : ui32, handshake.name = "addi5"} : <i6>
    %65:2 = fork [2] %64 {handshake.bb = 3 : ui32, handshake.name = "fork12"} : <i6>
    %66 = trunci %65#0 {handshake.bb = 3 : ui32, handshake.name = "trunci4"} : <i6> to <i5>
    %67 = constant %62 {handshake.bb = 3 : ui32, handshake.name = "constant21", value = 20 : i6} : <>, <i6>
    %68 = cmpi ult, %65#1, %67 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i6>
    %69:3 = fork [3] %68 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i1>
    %trueResult_23, %falseResult_24 = cond_br %69#0, %66 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <i5>
    sink %falseResult_24 {handshake.name = "sink6"} : <i5>
    %trueResult_25, %falseResult_26 = cond_br %69#1, %61#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %70 = constant %61#0 {handshake.bb = 3 : ui32, handshake.name = "constant22", value = false} : <>, <i1>
    %trueResult_27, %falseResult_28 = cond_br %69#2, %70 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i1>
    sink %trueResult_27 {handshake.name = "sink7"} : <i1>
    %71 = extui %falseResult_28 {handshake.bb = 4 : ui32, handshake.name = "extui22"} : <i1> to <i5>
    %72 = mux %index_30 [%71, %trueResult_53] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i5>, <i5>] to <i5>
    %73:4 = fork [4] %72 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i5>
    %result_29, %index_30 = control_merge [%falseResult_26, %trueResult_55]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %74:2 = fork [2] %result_29 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <>
    %75 = constant %74#0 {handshake.bb = 4 : ui32, handshake.name = "constant23", value = false} : <>, <i1>
    %76 = br %75 {handshake.bb = 4 : ui32, handshake.name = "br11"} : <i1>
    %77 = extui %76 {handshake.bb = 5 : ui32, handshake.name = "extui23"} : <i1> to <i5>
    %78 = br %73#3 {handshake.bb = 4 : ui32, handshake.name = "br12"} : <i5>
    %79 = br %73#0 {handshake.bb = 4 : ui32, handshake.name = "br13"} : <i5>
    %80 = br %73#1 {handshake.bb = 4 : ui32, handshake.name = "br14"} : <i5>
    %81 = br %73#2 {handshake.bb = 4 : ui32, handshake.name = "br15"} : <i5>
    %82 = br %74#1 {handshake.bb = 4 : ui32, handshake.name = "br16"} : <>
    %83 = mux %100#4 [%77, %trueResult_39] {handshake.bb = 5 : ui32, handshake.name = "mux7"} : <i1>, [<i5>, <i5>] to <i5>
    %84:4 = fork [4] %83 {handshake.bb = 5 : ui32, handshake.name = "fork16"} : <i5>
    %85 = extui %84#0 {handshake.bb = 5 : ui32, handshake.name = "extui24"} : <i5> to <i10>
    %86 = extui %84#1 {handshake.bb = 5 : ui32, handshake.name = "extui25"} : <i5> to <i10>
    %87 = extui %84#2 {handshake.bb = 5 : ui32, handshake.name = "extui26"} : <i5> to <i10>
    %88 = extui %84#3 {handshake.bb = 5 : ui32, handshake.name = "extui27"} : <i5> to <i6>
    %89 = constant %104 {handshake.bb = 5 : ui32, handshake.name = "constant24", value = 1 : i6} : <>, <i6>
    %90 = mux %100#3 [%78, %trueResult_41] {handshake.bb = 5 : ui32, handshake.name = "mux8"} : <i1>, [<i5>, <i5>] to <i5>
    %91 = mux %100#0 [%79, %trueResult_43] {handshake.bb = 5 : ui32, handshake.name = "mux9"} : <i1>, [<i5>, <i5>] to <i5>
    %92:2 = fork [2] %91 {handshake.bb = 5 : ui32, handshake.name = "fork17"} : <i5>
    %93 = extui %92#1 {handshake.bb = 5 : ui32, handshake.name = "extui28"} : <i5> to <i64>
    %94 = mux %100#1 [%80, %trueResult_45] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<i5>, <i5>] to <i5>
    %95:2 = fork [2] %94 {handshake.bb = 5 : ui32, handshake.name = "fork18"} : <i5>
    %96 = extui %95#1 {handshake.bb = 5 : ui32, handshake.name = "extui29"} : <i5> to <i64>
    %97 = mux %100#2 [%81, %trueResult_47] {handshake.bb = 5 : ui32, handshake.name = "mux11"} : <i1>, [<i5>, <i5>] to <i5>
    %98:2 = fork [2] %97 {handshake.bb = 5 : ui32, handshake.name = "fork19"} : <i5>
    %99 = extui %98#1 {handshake.bb = 5 : ui32, handshake.name = "extui30"} : <i5> to <i64>
    %result_31, %index_32 = control_merge [%82, %trueResult_49]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %100:5 = fork [5] %index_32 {handshake.bb = 5 : ui32, handshake.name = "fork20"} : <i1>
    %101:3 = fork [3] %result_31 {handshake.bb = 5 : ui32, handshake.name = "fork21"} : <>
    %102 = constant %101#1 {handshake.bb = 5 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %103 = source {handshake.bb = 5 : ui32, handshake.name = "source5"} : <>
    %104 = source {handshake.bb = 5 : ui32, handshake.name = "source6"} : <>
    %105 = source {handshake.bb = 5 : ui32, handshake.name = "source7"} : <>
    %106 = constant %105 {handshake.bb = 5 : ui32, handshake.name = "constant15", value = 5 : i64} : <>, <i64>
    %107:3 = fork [3] %106 {handshake.bb = 5 : ui32, handshake.name = "fork22"} : <i64>
    %108 = shli %93, %107#2 {handshake.bb = 5 : ui32, handshake.name = "shli3"} : <i64>
    %109 = trunci %108 {handshake.bb = 5 : ui32, handshake.name = "trunci5"} : <i64> to <i10>
    %110 = addi %109, %85 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i10>
    %addressResult_33, %dataResult_34 = load[%110] %1#0 {handshake.bb = 5 : ui32, handshake.name = "load3"} : <i10>, <i32>, <i10>, <i32>
    %111 = shli %96, %107#1 {handshake.bb = 5 : ui32, handshake.name = "shli4"} : <i64>
    %112 = trunci %111 {handshake.bb = 5 : ui32, handshake.name = "trunci6"} : <i64> to <i10>
    %113 = addi %112, %86 {handshake.bb = 5 : ui32, handshake.name = "addi8"} : <i10>
    %addressResult_35, %dataResult_36 = load[%113] %outputs {handshake.bb = 5 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : <i10>, <i32>, <i10>, <i32>
    %114 = muli %dataResult_34, %dataResult_36 {handshake.bb = 5 : ui32, handshake.name = "muli3"} : <i32>
    %115 = shli %99, %107#0 {handshake.bb = 5 : ui32, handshake.name = "shli5"} : <i64>
    %116 = trunci %115 {handshake.bb = 5 : ui32, handshake.name = "trunci7"} : <i64> to <i10>
    %117 = addi %116, %87 {handshake.bb = 5 : ui32, handshake.name = "addi9"} : <i10>
    %addressResult_37, %dataResult_38 = store[%117] %114 {handshake.bb = 5 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store5"} : <i10>, <i32>, <i10>, <i32>
    %118 = addi %88, %89 {handshake.bb = 5 : ui32, handshake.name = "addi10"} : <i6>
    %119:2 = fork [2] %118 {handshake.bb = 5 : ui32, handshake.name = "fork23"} : <i6>
    %120 = trunci %119#0 {handshake.bb = 5 : ui32, handshake.name = "trunci8"} : <i6> to <i5>
    %121 = constant %103 {handshake.bb = 5 : ui32, handshake.name = "constant25", value = -32 : i6} : <>, <i6>
    %122 = cmpi ult, %119#1, %121 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i6>
    %123:6 = fork [6] %122 {handshake.bb = 5 : ui32, handshake.name = "fork24"} : <i1>
    %trueResult_39, %falseResult_40 = cond_br %123#0, %120 {handshake.bb = 5 : ui32, handshake.name = "cond_br13"} : <i1>, <i5>
    sink %falseResult_40 {handshake.name = "sink8"} : <i5>
    %trueResult_41, %falseResult_42 = cond_br %123#4, %90 {handshake.bb = 5 : ui32, handshake.name = "cond_br14"} : <i1>, <i5>
    %trueResult_43, %falseResult_44 = cond_br %123#1, %92#0 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <i5>
    sink %falseResult_44 {handshake.name = "sink9"} : <i5>
    %trueResult_45, %falseResult_46 = cond_br %123#2, %95#0 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i5>
    sink %falseResult_46 {handshake.name = "sink10"} : <i5>
    %trueResult_47, %falseResult_48 = cond_br %123#3, %98#0 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <i5>
    sink %falseResult_48 {handshake.name = "sink11"} : <i5>
    %trueResult_49, %falseResult_50 = cond_br %123#5, %101#2 {handshake.bb = 5 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %124 = merge %falseResult_42 {handshake.bb = 6 : ui32, handshake.name = "merge1"} : <i5>
    %125 = extui %124 {handshake.bb = 6 : ui32, handshake.name = "extui31"} : <i5> to <i6>
    %126 = constant %128 {handshake.bb = 6 : ui32, handshake.name = "constant26", value = 1 : i6} : <>, <i6>
    %result_51, %index_52 = control_merge [%falseResult_50]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    sink %index_52 {handshake.name = "sink12"} : <i1>
    %127 = source {handshake.bb = 6 : ui32, handshake.name = "source8"} : <>
    %128 = source {handshake.bb = 6 : ui32, handshake.name = "source9"} : <>
    %129 = addi %125, %126 {handshake.bb = 6 : ui32, handshake.name = "addi11"} : <i6>
    %130:2 = fork [2] %129 {handshake.bb = 6 : ui32, handshake.name = "fork25"} : <i6>
    %131 = trunci %130#0 {handshake.bb = 6 : ui32, handshake.name = "trunci9"} : <i6> to <i5>
    %132 = constant %127 {handshake.bb = 6 : ui32, handshake.name = "constant27", value = 20 : i6} : <>, <i6>
    %133 = cmpi ult, %130#1, %132 {handshake.bb = 6 : ui32, handshake.name = "cmpi3"} : <i6>
    %134:2 = fork [2] %133 {handshake.bb = 6 : ui32, handshake.name = "fork26"} : <i1>
    %trueResult_53, %falseResult_54 = cond_br %134#0, %131 {handshake.bb = 6 : ui32, handshake.name = "cond_br19"} : <i1>, <i5>
    sink %falseResult_54 {handshake.name = "sink13"} : <i5>
    %trueResult_55, %falseResult_56 = cond_br %134#1, %result_51 {handshake.bb = 6 : ui32, handshake.name = "cond_br20"} : <i1>, <>
    %result_57, %index_58 = control_merge [%falseResult_56]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    sink %index_58 {handshake.name = "sink14"} : <i1>
    %135:5 = fork [5] %result_57 {handshake.bb = 7 : ui32, handshake.name = "fork27"} : <>
    end {handshake.bb = 7 : ui32, handshake.name = "end0"} %memEnd_4, %memEnd_2, %memEnd_0, %memEnd, %0#2 : <>, <>, <>, <>, <>
  }
}

