module {
  handshake.func @kmp(%arg0: memref<4xi8>, %arg1: memref<1000xi8>, %arg2: memref<4xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["pattern", "input", "kmpNext", "pattern_start", "input_start", "kmpNext_start", "start"], resNames = ["out0", "pattern_end", "input_end", "kmpNext_end", "end"]} {
    %0:3 = lazy_fork [3] %arg6 {handshake.bb = 0 : ui32, handshake.name = "lazy_fork0"} : <>
    %1:5 = fork [5] %0#2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %2:4 = lsq[%arg2 : memref<4xi32>] (%arg5, %0#0, %addressResult, %dataResult, %33#0, %addressResult_24, %48#0, %addressResult_38, %dataResult_39, %93#0, %addressResult_78, %121#0, %addressResult_104, %146#2)  {groupSizes = [1 : i32, 1 : i32, 1 : i32, 1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i2>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i2>, !handshake.control<>, !handshake.channel<i2>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xi8>] %arg4 (%addressResult_50) %146#1 {connectedBlocks = [5 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i10>) -> !handshake.channel<i8>
    %outputs_0:5, %memEnd_1 = mem_controller[%arg0 : memref<4xi8>] %arg3 (%addressResult_2, %addressResult_12, %addressResult_36, %addressResult_64, %addressResult_92) %146#0 {connectedBlocks = [1 : i32, 2 : i32, 4 : i32, 6 : i32, 8 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i2>) -> (!handshake.channel<i8>, !handshake.channel<i8>, !handshake.channel<i8>, !handshake.channel<i8>, !handshake.channel<i8>)
    %3 = constant %1#4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = constant %1#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 0 : i2} : <>, <i2>
    %addressResult, %dataResult = store[%4] %3 {handshake.bb = 0 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store0"} : <i2>, <i32>, <i2>, <i32>
    %5 = constant %1#1 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %6 = br %5 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %7 = extui %6 {handshake.bb = 0 : ui32, handshake.name = "extui4"} : <i1> to <i32>
    %8 = constant %1#2 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = true} : <>, <i1>
    %9 = br %8 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i1>
    %10 = extui %9 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i1> to <i2>
    %11 = br %0#1 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %12 = mux %16#1 [%7, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %13:2 = fork [2] %12 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %14 = mux %16#0 [%10, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i2>, <i2>] to <i2>
    %15:2 = fork [2] %14 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i2>
    %result, %index = control_merge [%11, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %16:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i1>
    %17 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %18 = constant %17 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %addressResult_2, %dataResult_3 = load[%15#0] %outputs_0#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i2>, <i8>, <i2>, <i8>
    %19 = cmpi sgt, %13#1, %18 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %20:4 = fork [4] %19 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult, %falseResult = cond_br %20#3, %13#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %20#0, %15#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i2>
    %trueResult_6, %falseResult_7 = cond_br %20#2, %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i8>
    %trueResult_8, %falseResult_9 = cond_br %20#1, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %21 = mux %27#1 [%trueResult, %trueResult_26] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %22:2 = fork [2] %21 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i32>
    %23 = trunci %22#0 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i32> to <i2>
    %24 = mux %27#0 [%trueResult_4, %trueResult_28] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i2>, <i2>] to <i2>
    %25 = mux %27#2 [%trueResult_6, %trueResult_30] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i8>, <i8>] to <i8>
    %26:2 = fork [2] %25 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i8>
    %result_10, %index_11 = control_merge [%trueResult_8, %trueResult_32]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %27:3 = fork [3] %index_11 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i1>
    %addressResult_12, %dataResult_13 = load[%23] %outputs_0#1 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : <i2>, <i8>, <i2>, <i8>
    %28 = cmpi eq, %dataResult_13, %26#1 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i8>
    %29:4 = fork [4] %28 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_14, %falseResult_15 = cond_br %29#3, %22#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    sink %falseResult_15 {handshake.name = "sink0"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %29#0, %24 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i2>
    %trueResult_18, %falseResult_19 = cond_br %29#2, %26#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i8>
    %trueResult_20, %falseResult_21 = cond_br %29#1, %result_10 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %30 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i2>
    %31:2 = fork [2] %30 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i2>
    %32 = merge %falseResult_19 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i8>
    %result_22, %index_23 = control_merge [%falseResult_21]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_23 {handshake.name = "sink1"} : <i1>
    %33:2 = lazy_fork [2] %result_22 {handshake.bb = 3 : ui32, handshake.name = "lazy_fork1"} : <>
    %34 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %35 = constant %34 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %addressResult_24, %dataResult_25 = load[%31#0] %2#0 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load3"} : <i2>, <i32>, <i2>, <i32>
    %36:2 = fork [2] %dataResult_25 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %37 = cmpi sgt, %36#0, %35 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %38:4 = fork [4] %37 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult_26, %falseResult_27 = cond_br %38#3, %36#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %38#0, %31#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br18"} : <i1>, <i2>
    %trueResult_30, %falseResult_31 = cond_br %38#2, %32 {handshake.bb = 3 : ui32, handshake.name = "cond_br19"} : <i1>, <i8>
    %trueResult_32, %falseResult_33 = cond_br %38#1, %33#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br20"} : <i1>, <>
    %39 = mux %47#1 [%falseResult, %trueResult_14, %falseResult_27] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %40:3 = fork [3] %39 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <i32>
    %41 = trunci %40#0 {handshake.bb = 4 : ui32, handshake.name = "trunci1"} : <i32> to <i2>
    %42 = mux %47#0 [%falseResult_5, %trueResult_16, %falseResult_29] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i2>, [<i2>, <i2>, <i2>] to <i2>
    %43:2 = fork [2] %42 {handshake.bb = 4 : ui32, handshake.name = "fork13"} : <i2>
    %44 = extui %43#1 {handshake.bb = 4 : ui32, handshake.name = "extui6"} : <i2> to <i3>
    %45 = constant %51#0 {handshake.bb = 4 : ui32, handshake.name = "constant5", value = 1 : i3} : <>, <i3>
    %46 = mux %47#2 [%falseResult_7, %trueResult_18, %falseResult_31] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i2>, [<i8>, <i8>, <i8>] to <i8>
    %result_34, %index_35 = control_merge [%falseResult_9, %trueResult_20, %falseResult_33]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>, <>] to <>, <i2>
    %47:3 = fork [3] %index_35 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i2>
    %48:3 = lazy_fork [3] %result_34 {handshake.bb = 4 : ui32, handshake.name = "lazy_fork2"} : <>
    %49 = source {handshake.bb = 4 : ui32, handshake.name = "source2"} : <>
    %50 = source {handshake.bb = 4 : ui32, handshake.name = "source3"} : <>
    %51:2 = fork [2] %50 {handshake.bb = 4 : ui32, handshake.name = "fork15"} : <>
    %52 = constant %51#1 {handshake.bb = 4 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %addressResult_36, %dataResult_37 = load[%41] %outputs_0#2 {handshake.bb = 4 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : <i2>, <i8>, <i2>, <i8>
    %53 = cmpi eq, %dataResult_37, %46 {handshake.bb = 4 : ui32, handshake.name = "cmpi3"} : <i8>
    %54 = addi %40#2, %52 {handshake.bb = 4 : ui32, handshake.name = "addi0"} : <i32>
    %55 = select %53[%54, %40#1] {handshake.bb = 4 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %56:2 = fork [2] %55 {handshake.bb = 4 : ui32, handshake.name = "fork16"} : <i32>
    %addressResult_38, %dataResult_39 = store[%43#0] %56#0 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store5"} : <i2>, <i32>, <i2>, <i32>
    %57 = addi %44, %45 {handshake.bb = 4 : ui32, handshake.name = "addi1"} : <i3>
    %58:2 = fork [2] %57 {handshake.bb = 4 : ui32, handshake.name = "fork17"} : <i3>
    %59 = trunci %58#0 {handshake.bb = 4 : ui32, handshake.name = "trunci2"} : <i3> to <i2>
    %60 = constant %49 {handshake.bb = 4 : ui32, handshake.name = "constant20", value = -4 : i3} : <>, <i3>
    %61 = cmpi ult, %58#1, %60 {handshake.bb = 4 : ui32, handshake.name = "cmpi4"} : <i3>
    %62:4 = fork [4] %61 {handshake.bb = 4 : ui32, handshake.name = "fork18"} : <i1>
    %trueResult_40, %falseResult_41 = cond_br %62#1, %56#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    sink %falseResult_41 {handshake.name = "sink2"} : <i32>
    %trueResult_42, %falseResult_43 = cond_br %62#0, %59 {handshake.bb = 4 : ui32, handshake.name = "cond_br22"} : <i1>, <i2>
    sink %falseResult_43 {handshake.name = "sink3"} : <i2>
    %trueResult_44, %falseResult_45 = cond_br %62#2, %48#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br23"} : <i1>, <>
    %63 = constant %48#2 {handshake.bb = 4 : ui32, handshake.name = "constant21", value = false} : <>, <i1>
    %trueResult_46, %falseResult_47 = cond_br %62#3, %63 {handshake.bb = 4 : ui32, handshake.name = "cond_br24"} : <i1>, <i1>
    %64:2 = fork [2] %falseResult_47 {handshake.bb = 4 : ui32, handshake.name = "fork19"} : <i1>
    sink %trueResult_46 {handshake.name = "sink4"} : <i1>
    %65 = extui %64#1 {handshake.bb = 4 : ui32, handshake.name = "extui7"} : <i1> to <i32>
    %66:2 = fork [2] %65 {handshake.bb = 4 : ui32, handshake.name = "fork20"} : <i32>
    %67 = extui %64#0 {handshake.bb = 5 : ui32, handshake.name = "extui8"} : <i1> to <i10>
    %68 = mux %73#1 [%66#0, %trueResult_108] {handshake.bb = 5 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %69 = mux %73#2 [%66#1, %trueResult_110] {handshake.bb = 5 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %70:2 = fork [2] %69 {handshake.bb = 5 : ui32, handshake.name = "fork21"} : <i32>
    %71 = mux %73#0 [%67, %trueResult_112] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<i10>, <i10>] to <i10>
    %72:2 = fork [2] %71 {handshake.bb = 5 : ui32, handshake.name = "fork22"} : <i10>
    %result_48, %index_49 = control_merge [%falseResult_45, %trueResult_114]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %73:3 = fork [3] %index_49 {handshake.bb = 5 : ui32, handshake.name = "fork23"} : <i1>
    %74 = source {handshake.bb = 5 : ui32, handshake.name = "source4"} : <>
    %75 = constant %74 {handshake.bb = 5 : ui32, handshake.name = "constant12", value = 0 : i32} : <>, <i32>
    %addressResult_50, %dataResult_51 = load[%72#0] %outputs {handshake.bb = 5 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load6"} : <i10>, <i8>, <i10>, <i8>
    %76 = cmpi sgt, %70#1, %75 {handshake.bb = 5 : ui32, handshake.name = "cmpi5"} : <i32>
    %77:5 = fork [5] %76 {handshake.bb = 5 : ui32, handshake.name = "fork24"} : <i1>
    %trueResult_52, %falseResult_53 = cond_br %77#4, %70#0 {handshake.bb = 5 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_54, %falseResult_55 = cond_br %77#3, %68 {handshake.bb = 5 : ui32, handshake.name = "cond_br26"} : <i1>, <i32>
    %trueResult_56, %falseResult_57 = cond_br %77#0, %72#1 {handshake.bb = 5 : ui32, handshake.name = "cond_br27"} : <i1>, <i10>
    %trueResult_58, %falseResult_59 = cond_br %77#2, %dataResult_51 {handshake.bb = 5 : ui32, handshake.name = "cond_br28"} : <i1>, <i8>
    %trueResult_60, %falseResult_61 = cond_br %77#1, %result_48 {handshake.bb = 5 : ui32, handshake.name = "cond_br29"} : <i1>, <>
    %78 = mux %85#1 [%trueResult_52, %trueResult_80] {handshake.bb = 6 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %79:2 = fork [2] %78 {handshake.bb = 6 : ui32, handshake.name = "fork25"} : <i32>
    %80 = trunci %79#0 {handshake.bb = 6 : ui32, handshake.name = "trunci3"} : <i32> to <i2>
    %81 = mux %85#2 [%trueResult_54, %trueResult_82] {handshake.bb = 6 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %82 = mux %85#0 [%trueResult_56, %trueResult_84] {handshake.bb = 6 : ui32, handshake.name = "mux13"} : <i1>, [<i10>, <i10>] to <i10>
    %83 = mux %85#3 [%trueResult_58, %trueResult_86] {handshake.bb = 6 : ui32, handshake.name = "mux14"} : <i1>, [<i8>, <i8>] to <i8>
    %84:2 = fork [2] %83 {handshake.bb = 6 : ui32, handshake.name = "fork26"} : <i8>
    %result_62, %index_63 = control_merge [%trueResult_60, %trueResult_88]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %85:4 = fork [4] %index_63 {handshake.bb = 6 : ui32, handshake.name = "fork27"} : <i1>
    %addressResult_64, %dataResult_65 = load[%80] %outputs_0#3 {handshake.bb = 6 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load7"} : <i2>, <i8>, <i2>, <i8>
    %86 = cmpi eq, %dataResult_65, %84#1 {handshake.bb = 6 : ui32, handshake.name = "cmpi6"} : <i8>
    %87:5 = fork [5] %86 {handshake.bb = 6 : ui32, handshake.name = "fork28"} : <i1>
    %trueResult_66, %falseResult_67 = cond_br %87#4, %79#1 {handshake.bb = 6 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %88 = trunci %falseResult_67 {handshake.bb = 6 : ui32, handshake.name = "trunci4"} : <i32> to <i2>
    %trueResult_68, %falseResult_69 = cond_br %87#3, %81 {handshake.bb = 6 : ui32, handshake.name = "cond_br31"} : <i1>, <i32>
    %trueResult_70, %falseResult_71 = cond_br %87#0, %82 {handshake.bb = 6 : ui32, handshake.name = "cond_br32"} : <i1>, <i10>
    %trueResult_72, %falseResult_73 = cond_br %87#2, %84#0 {handshake.bb = 6 : ui32, handshake.name = "cond_br33"} : <i1>, <i8>
    %trueResult_74, %falseResult_75 = cond_br %87#1, %result_62 {handshake.bb = 6 : ui32, handshake.name = "cond_br34"} : <i1>, <>
    %89 = merge %falseResult_69 {handshake.bb = 7 : ui32, handshake.name = "merge2"} : <i32>
    %90 = merge %falseResult_71 {handshake.bb = 7 : ui32, handshake.name = "merge3"} : <i10>
    %91 = merge %falseResult_73 {handshake.bb = 7 : ui32, handshake.name = "merge4"} : <i8>
    %92 = merge %88 {handshake.bb = 7 : ui32, handshake.name = "merge5"} : <i2>
    %result_76, %index_77 = control_merge [%falseResult_75]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    sink %index_77 {handshake.name = "sink5"} : <i1>
    %93:2 = lazy_fork [2] %result_76 {handshake.bb = 7 : ui32, handshake.name = "lazy_fork3"} : <>
    %94 = source {handshake.bb = 7 : ui32, handshake.name = "source5"} : <>
    %95 = constant %94 {handshake.bb = 7 : ui32, handshake.name = "constant13", value = 0 : i32} : <>, <i32>
    %addressResult_78, %dataResult_79 = load[%92] %2#1 {handshake.bb = 7 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 3>, handshake.name = "load8"} : <i2>, <i32>, <i2>, <i32>
    %96:2 = fork [2] %dataResult_79 {handshake.bb = 7 : ui32, handshake.name = "fork29"} : <i32>
    %97 = cmpi sgt, %96#0, %95 {handshake.bb = 7 : ui32, handshake.name = "cmpi7"} : <i32>
    %98:5 = fork [5] %97 {handshake.bb = 7 : ui32, handshake.name = "fork30"} : <i1>
    %trueResult_80, %falseResult_81 = cond_br %98#4, %96#1 {handshake.bb = 7 : ui32, handshake.name = "cond_br35"} : <i1>, <i32>
    %trueResult_82, %falseResult_83 = cond_br %98#3, %89 {handshake.bb = 7 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    %trueResult_84, %falseResult_85 = cond_br %98#0, %90 {handshake.bb = 7 : ui32, handshake.name = "cond_br37"} : <i1>, <i10>
    %trueResult_86, %falseResult_87 = cond_br %98#2, %91 {handshake.bb = 7 : ui32, handshake.name = "cond_br38"} : <i1>, <i8>
    %trueResult_88, %falseResult_89 = cond_br %98#1, %93#1 {handshake.bb = 7 : ui32, handshake.name = "cond_br39"} : <i1>, <>
    %99 = mux %105#1 [%falseResult_53, %trueResult_66, %falseResult_81] {handshake.bb = 8 : ui32, handshake.name = "mux15"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %100:3 = fork [3] %99 {handshake.bb = 8 : ui32, handshake.name = "fork31"} : <i32>
    %101 = trunci %100#0 {handshake.bb = 8 : ui32, handshake.name = "trunci5"} : <i32> to <i2>
    %102 = mux %105#2 [%falseResult_55, %trueResult_68, %falseResult_83] {handshake.bb = 8 : ui32, handshake.name = "mux16"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %103 = mux %105#0 [%falseResult_57, %trueResult_70, %falseResult_85] {handshake.bb = 8 : ui32, handshake.name = "mux17"} : <i2>, [<i10>, <i10>, <i10>] to <i10>
    %104 = mux %105#3 [%falseResult_59, %trueResult_72, %falseResult_87] {handshake.bb = 8 : ui32, handshake.name = "mux18"} : <i2>, [<i8>, <i8>, <i8>] to <i8>
    %result_90, %index_91 = control_merge [%falseResult_61, %trueResult_74, %falseResult_89]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>, <>] to <>, <i2>
    %105:4 = fork [4] %index_91 {handshake.bb = 8 : ui32, handshake.name = "fork32"} : <i2>
    %106 = source {handshake.bb = 8 : ui32, handshake.name = "source6"} : <>
    %107 = constant %106 {handshake.bb = 8 : ui32, handshake.name = "constant14", value = 3 : i32} : <>, <i32>
    %108 = source {handshake.bb = 8 : ui32, handshake.name = "source7"} : <>
    %109 = constant %108 {handshake.bb = 8 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %addressResult_92, %dataResult_93 = load[%101] %outputs_0#4 {handshake.bb = 8 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load9"} : <i2>, <i8>, <i2>, <i8>
    %110 = cmpi eq, %dataResult_93, %104 {handshake.bb = 8 : ui32, handshake.name = "cmpi8"} : <i8>
    %111 = addi %100#2, %109 {handshake.bb = 8 : ui32, handshake.name = "addi2"} : <i32>
    %112 = select %110[%111, %100#1] {handshake.bb = 8 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %113:2 = fork [2] %112 {handshake.bb = 8 : ui32, handshake.name = "fork33"} : <i32>
    %114 = cmpi sgt, %113#1, %107 {handshake.bb = 8 : ui32, handshake.name = "cmpi9"} : <i32>
    %115:4 = fork [4] %114 {handshake.bb = 8 : ui32, handshake.name = "fork34"} : <i1>
    %trueResult_94, %falseResult_95 = cond_br %115#3, %102 {handshake.bb = 8 : ui32, handshake.name = "cond_br40"} : <i1>, <i32>
    %trueResult_96, %falseResult_97 = cond_br %115#0, %103 {handshake.bb = 8 : ui32, handshake.name = "cond_br41"} : <i1>, <i10>
    %trueResult_98, %falseResult_99 = cond_br %115#2, %113#0 {handshake.bb = 8 : ui32, handshake.name = "cond_br42"} : <i1>, <i32>
    %116 = trunci %trueResult_98 {handshake.bb = 8 : ui32, handshake.name = "trunci6"} : <i32> to <i2>
    %trueResult_100, %falseResult_101 = cond_br %115#1, %result_90 {handshake.bb = 8 : ui32, handshake.name = "cond_br43"} : <i1>, <>
    %117 = merge %trueResult_94 {handshake.bb = 9 : ui32, handshake.name = "merge6"} : <i32>
    %118 = merge %trueResult_96 {handshake.bb = 9 : ui32, handshake.name = "merge7"} : <i10>
    %119 = merge %116 {handshake.bb = 9 : ui32, handshake.name = "merge8"} : <i2>
    %120 = constant %122 {handshake.bb = 9 : ui32, handshake.name = "constant22", value = -1 : i2} : <>, <i2>
    %result_102, %index_103 = control_merge [%trueResult_100]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    sink %index_103 {handshake.name = "sink6"} : <i1>
    %121:2 = lazy_fork [2] %result_102 {handshake.bb = 9 : ui32, handshake.name = "lazy_fork4"} : <>
    %122 = source {handshake.bb = 9 : ui32, handshake.name = "source8"} : <>
    %123 = source {handshake.bb = 9 : ui32, handshake.name = "source9"} : <>
    %124 = constant %123 {handshake.bb = 9 : ui32, handshake.name = "constant17", value = 1 : i32} : <>, <i32>
    %125 = addi %117, %124 {handshake.bb = 9 : ui32, handshake.name = "addi3"} : <i32>
    %126 = addi %119, %120 {handshake.bb = 9 : ui32, handshake.name = "addi4"} : <i2>
    %addressResult_104, %dataResult_105 = load[%126] %2#2 {handshake.bb = 9 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 4>, handshake.name = "load10"} : <i2>, <i32>, <i2>, <i32>
    %127 = br %dataResult_105 {handshake.bb = 9 : ui32, handshake.name = "br5"} : <i32>
    %128 = br %125 {handshake.bb = 9 : ui32, handshake.name = "br6"} : <i32>
    %129 = br %118 {handshake.bb = 9 : ui32, handshake.name = "br7"} : <i10>
    %130 = br %121#1 {handshake.bb = 9 : ui32, handshake.name = "br8"} : <>
    %131 = mux %136#1 [%falseResult_99, %127] {handshake.bb = 10 : ui32, handshake.name = "mux19"} : <i1>, [<i32>, <i32>] to <i32>
    %132 = mux %136#2 [%falseResult_95, %128] {handshake.bb = 10 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %133 = mux %136#0 [%falseResult_97, %129] {handshake.bb = 10 : ui32, handshake.name = "mux21"} : <i1>, [<i10>, <i10>] to <i10>
    %134 = extui %133 {handshake.bb = 10 : ui32, handshake.name = "extui9"} : <i10> to <i11>
    %135 = constant %138 {handshake.bb = 10 : ui32, handshake.name = "constant23", value = 1 : i11} : <>, <i11>
    %result_106, %index_107 = control_merge [%falseResult_101, %130]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>, <>] to <>, <i1>
    %136:3 = fork [3] %index_107 {handshake.bb = 10 : ui32, handshake.name = "fork35"} : <i1>
    %137 = source {handshake.bb = 10 : ui32, handshake.name = "source10"} : <>
    %138 = source {handshake.bb = 10 : ui32, handshake.name = "source11"} : <>
    %139 = addi %134, %135 {handshake.bb = 10 : ui32, handshake.name = "addi5"} : <i11>
    %140:2 = fork [2] %139 {handshake.bb = 10 : ui32, handshake.name = "fork36"} : <i11>
    %141 = trunci %140#0 {handshake.bb = 10 : ui32, handshake.name = "trunci7"} : <i11> to <i10>
    %142 = constant %137 {handshake.bb = 10 : ui32, handshake.name = "constant24", value = 1000 : i11} : <>, <i11>
    %143 = cmpi ult, %140#1, %142 {handshake.bb = 10 : ui32, handshake.name = "cmpi10"} : <i11>
    %144:4 = fork [4] %143 {handshake.bb = 10 : ui32, handshake.name = "fork37"} : <i1>
    %trueResult_108, %falseResult_109 = cond_br %144#1, %132 {handshake.bb = 10 : ui32, handshake.name = "cond_br44"} : <i1>, <i32>
    %trueResult_110, %falseResult_111 = cond_br %144#2, %131 {handshake.bb = 10 : ui32, handshake.name = "cond_br45"} : <i1>, <i32>
    sink %falseResult_111 {handshake.name = "sink7"} : <i32>
    %trueResult_112, %falseResult_113 = cond_br %144#0, %141 {handshake.bb = 10 : ui32, handshake.name = "cond_br46"} : <i1>, <i10>
    sink %falseResult_113 {handshake.name = "sink8"} : <i10>
    %trueResult_114, %falseResult_115 = cond_br %144#3, %result_106 {handshake.bb = 10 : ui32, handshake.name = "cond_br47"} : <i1>, <>
    %145 = merge %falseResult_109 {handshake.bb = 11 : ui32, handshake.name = "merge9"} : <i32>
    %result_116, %index_117 = control_merge [%falseResult_115]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>] to <>, <i1>
    sink %index_117 {handshake.name = "sink9"} : <i1>
    %146:3 = fork [3] %result_116 {handshake.bb = 11 : ui32, handshake.name = "fork38"} : <>
    end {handshake.bb = 11 : ui32, handshake.name = "end0"} %145, %memEnd_1, %memEnd, %2#3, %1#3 : <i32>, <>, <>, <>, <>
  }
}

