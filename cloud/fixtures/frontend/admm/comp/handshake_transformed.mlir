module {
  handshake.func @admm(%arg0: !handshake.channel<f32>, %arg1: memref<30xf32>, %arg2: memref<900xf32>, %arg3: memref<2xf32>, %arg4: memref<30xf32>, %arg5: memref<30xf32>, %arg6: memref<30xf32>, %arg7: memref<30xf32>, %arg8: memref<30xf32>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, %arg11: !handshake.control<>, %arg12: !handshake.control<>, %arg13: !handshake.control<>, %arg14: !handshake.control<>, %arg15: !handshake.control<>, %arg16: !handshake.control<>, %arg17: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["vdc", "inp", "KKT_inv", "out", "x", "z", "y", "rhs", "temp_x_tilde", "inp_start", "KKT_inv_start", "out_start", "x_start", "z_start", "y_start", "rhs_start", "temp_x_tilde_start", "start"], resNames = ["inp_end", "KKT_inv_end", "out_end", "x_end", "z_end", "y_end", "rhs_end", "temp_x_tilde_end", "end"]} {
    %0:3 = fork [3] %arg17 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:4 = lsq[%arg8 : memref<30xf32>] (%arg16, %62#0, %addressResult_21, %dataResult_22, %81#0, %addressResult_37, %110#0, %addressResult_45, %dataResult_46, %151#0, %addressResult_67, %addressResult_73, %220#12)  {groupSizes = [1 : i32, 1 : i32, 1 : i32, 2 : i32], handshake.name = "lsq5"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i5>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i5>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %2:4 = lsq[%arg7 : memref<30xf32>] (%arg15, %17#0, %addressResult_3, %dataResult_4, %110#2, %addressResult_43, %193#0, %addressResult_105, %dataResult_106, %220#10, %addressResult_129, %addressResult_133, %220#11)  {groupSizes = [1 : i32, 1 : i32, 1 : i32, 2 : i32], handshake.name = "lsq6"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i5>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i5>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %3:4 = lsq[%arg6 : memref<30xf32>] (%arg14, %17#2, %addressResult_9, %dataResult_10, %151#2, %addressResult_77, %addressResult_81, %addressResult_83, %dataResult_84, %193#2, %addressResult_103, %220#9)  {groupSizes = [1 : i32, 3 : i32, 1 : i32], handshake.name = "lsq7"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i5>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i5>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %4:3 = lsq[%arg5 : memref<30xf32>] (%arg13, %17#3, %addressResult_7, %dataResult_8, %151#3, %addressResult_75, %addressResult_79, %dataResult_80, %193#3, %addressResult_101, %220#8)  {groupSizes = [1 : i32, 2 : i32, 1 : i32], handshake.name = "lsq8"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i5>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %5:3 = lsq[%arg4 : memref<30xf32>] (%arg12, %17#4, %addressResult_5, %dataResult_6, %151#4, %addressResult_69, %addressResult_71, %dataResult_72, %193#4, %addressResult_99, %220#7)  {groupSizes = [1 : i32, 2 : i32, 1 : i32], handshake.name = "lsq9"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i5>, !handshake.channel<i5>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i5>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %memEnd = mem_controller[%arg3 : memref<2xf32>] %arg11 (%221, %addressResult_131, %dataResult_132, %addressResult_135, %dataResult_136) %220#6 {connectedBlocks = [10 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i1>, !handshake.channel<f32>, !handshake.channel<i1>, !handshake.channel<f32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg2 : memref<900xf32>] %arg10 (%addressResult_41) %220#5 {connectedBlocks = [6 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i10>) -> !handshake.channel<f32>
    %outputs_1, %memEnd_2 = mem_controller[%arg1 : memref<30xf32>] %arg9 (%addressResult) %220#4 {connectedBlocks = [1 : i32], handshake.name = "mem_controller5"} :    (!handshake.channel<i5>) -> !handshake.channel<f32>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %7 = br %6 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <i1>
    %8 = extui %7 {handshake.bb = 1 : ui32, handshake.name = "extui23"} : <i1> to <i5>
    %9 = br %arg0 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <f32>
    %10 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %11 = mux %16#0 [%8, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i5>, <i5>] to <i5>
    %12:6 = fork [6] %11 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i5>
    %13 = extui %12#5 {handshake.bb = 1 : ui32, handshake.name = "extui24"} : <i5> to <i6>
    %14 = constant %19 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i6} : <>, <i6>
    %15 = mux %16#1 [%9, %trueResult_11] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%10, %trueResult_13]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %16:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %17:6 = lazy_fork [6] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %18 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %20 = constant %17#5 {handshake.bb = 1 : ui32, handshake.name = "constant18", value = 0.000000e+00 : f32} : <>, <f32>
    %21:3 = fork [3] %20 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <f32>
    %addressResult, %dataResult = load[%12#4] %outputs_1 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i5>, <f32>, <i5>, <f32>
    %22 = negf %dataResult {fastmath = #arith.fastmath<none>, handshake.bb = 1 : ui32, handshake.name = "negf0"} : <f32>
    %addressResult_3, %dataResult_4 = store[%12#3] %22 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load23", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load25", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store22", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : <i5>, <f32>, <i5>, <f32>
    %addressResult_5, %dataResult_6 = store[%12#2] %21#2 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load11", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load19", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store12", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : <i5>, <f32>, <i5>, <f32>
    %addressResult_7, %dataResult_8 = store[%12#1] %21#1 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load20", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store16", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store3"} : <i5>, <f32>, <i5>, <f32>
    %addressResult_9, %dataResult_10 = store[%12#0] %21#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load17", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load21", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store18", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store4"} : <i5>, <f32>, <i5>, <f32>
    %23 = addi %13, %14 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i6>
    %24:2 = fork [2] %23 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i6>
    %25 = trunci %24#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i6> to <i5>
    %26 = constant %18 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 30 : i6} : <>, <i6>
    %27 = cmpi ult, %24#1, %26 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i6>
    %28:3 = fork [3] %27 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %trueResult, %falseResult = cond_br %28#0, %25 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i5>
    sink %falseResult {handshake.name = "sink0"} : <i5>
    %trueResult_11, %falseResult_12 = cond_br %28#1, %15 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <f32>
    %trueResult_13, %falseResult_14 = cond_br %28#2, %17#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %29 = merge %falseResult_12 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <f32>
    %result_15, %index_16 = control_merge [%falseResult_14]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_16 {handshake.name = "sink1"} : <i1>
    %30:2 = fork [2] %result_15 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <>
    %31 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %32 = constant %31 {handshake.bb = 2 : ui32, handshake.name = "constant19", value = 5.000000e-01 : f32} : <>, <f32>
    %33 = mulf %29, %32 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "mulf0"} : <f32>
    %34:2 = fork [2] %33 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <f32>
    %35 = negf %34#1 {fastmath = #arith.fastmath<none>, handshake.bb = 2 : ui32, handshake.name = "negf1"} : <f32>
    %36 = constant %30#0 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = false} : <>, <i1>
    %37 = br %36 {handshake.bb = 2 : ui32, handshake.name = "br7"} : <i1>
    %38 = extui %37 {handshake.bb = 3 : ui32, handshake.name = "extui25"} : <i1> to <i3>
    %39 = br %34#0 {handshake.bb = 2 : ui32, handshake.name = "br8"} : <f32>
    %40 = br %35 {handshake.bb = 2 : ui32, handshake.name = "br9"} : <f32>
    %41 = br %30#1 {handshake.bb = 2 : ui32, handshake.name = "br10"} : <>
    %42 = mux %45#0 [%38, %trueResult_119] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i3>, <i3>] to <i3>
    %43 = mux %45#1 [%39, %trueResult_121] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<f32>, <f32>] to <f32>
    %44 = mux %45#2 [%40, %trueResult_123] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %result_17, %index_18 = control_merge [%41, %trueResult_125]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %45:3 = fork [3] %index_18 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i1>
    %46:2 = fork [2] %result_17 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <>
    %47 = constant %46#0 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = false} : <>, <i1>
    %48 = br %47 {handshake.bb = 3 : ui32, handshake.name = "br11"} : <i1>
    %49 = extui %48 {handshake.bb = 4 : ui32, handshake.name = "extui26"} : <i1> to <i5>
    %50 = br %43 {handshake.bb = 3 : ui32, handshake.name = "br12"} : <f32>
    %51 = br %44 {handshake.bb = 3 : ui32, handshake.name = "br13"} : <f32>
    %52 = br %42 {handshake.bb = 3 : ui32, handshake.name = "br14"} : <i3>
    %53 = br %46#1 {handshake.bb = 3 : ui32, handshake.name = "br15"} : <>
    %54 = mux %61#1 [%49, %trueResult_23] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i5>, <i5>] to <i5>
    %55:2 = fork [2] %54 {handshake.bb = 4 : ui32, handshake.name = "fork10"} : <i5>
    %56 = extui %55#1 {handshake.bb = 4 : ui32, handshake.name = "extui27"} : <i5> to <i6>
    %57 = constant %65 {handshake.bb = 4 : ui32, handshake.name = "constant8", value = 1 : i6} : <>, <i6>
    %58 = mux %61#2 [%50, %trueResult_25] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<f32>, <f32>] to <f32>
    %59 = mux %61#3 [%51, %trueResult_27] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<f32>, <f32>] to <f32>
    %60 = mux %61#0 [%52, %trueResult_29] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i3>, <i3>] to <i3>
    %result_19, %index_20 = control_merge [%53, %trueResult_31]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %61:4 = fork [4] %index_20 {handshake.bb = 4 : ui32, handshake.name = "fork11"} : <i1>
    %62:3 = lazy_fork [3] %result_19 {handshake.bb = 4 : ui32, handshake.name = "lazy_fork1"} : <>
    %63:2 = fork [2] %62#2 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <>
    %64 = source {handshake.bb = 4 : ui32, handshake.name = "source3"} : <>
    %65 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %66 = constant %63#1 {handshake.bb = 4 : ui32, handshake.name = "constant24", value = 0.000000e+00 : f32} : <>, <f32>
    %addressResult_21, %dataResult_22 = store[%55#0] %66 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load13", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store9", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store5"} : <i5>, <f32>, <i5>, <f32>
    %67 = addi %56, %57 {handshake.bb = 4 : ui32, handshake.name = "addi1"} : <i6>
    %68:2 = fork [2] %67 {handshake.bb = 4 : ui32, handshake.name = "fork13"} : <i6>
    %69 = trunci %68#0 {handshake.bb = 4 : ui32, handshake.name = "trunci1"} : <i6> to <i5>
    %70 = constant %64 {handshake.bb = 4 : ui32, handshake.name = "constant9", value = 30 : i6} : <>, <i6>
    %71 = cmpi ult, %68#1, %70 {handshake.bb = 4 : ui32, handshake.name = "cmpi1"} : <i6>
    %72:6 = fork [6] %71 {handshake.bb = 4 : ui32, handshake.name = "fork14"} : <i1>
    %trueResult_23, %falseResult_24 = cond_br %72#0, %69 {handshake.bb = 4 : ui32, handshake.name = "cond_br9"} : <i1>, <i5>
    sink %falseResult_24 {handshake.name = "sink2"} : <i5>
    %trueResult_25, %falseResult_26 = cond_br %72#2, %58 {handshake.bb = 4 : ui32, handshake.name = "cond_br10"} : <i1>, <f32>
    %trueResult_27, %falseResult_28 = cond_br %72#3, %59 {handshake.bb = 4 : ui32, handshake.name = "cond_br11"} : <i1>, <f32>
    %trueResult_29, %falseResult_30 = cond_br %72#1, %60 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i3>
    %trueResult_31, %falseResult_32 = cond_br %72#4, %62#1 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %73 = constant %63#0 {handshake.bb = 4 : ui32, handshake.name = "constant10", value = false} : <>, <i1>
    %trueResult_33, %falseResult_34 = cond_br %72#5, %73 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i1>
    sink %trueResult_33 {handshake.name = "sink3"} : <i1>
    %74 = extui %falseResult_34 {handshake.bb = 5 : ui32, handshake.name = "extui28"} : <i1> to <i5>
    %75 = mux %80#1 [%74, %trueResult_85] {handshake.bb = 5 : ui32, handshake.name = "mux9"} : <i1>, [<i5>, <i5>] to <i5>
    %76:4 = fork [4] %75 {handshake.bb = 5 : ui32, handshake.name = "fork15"} : <i5>
    %77 = mux %80#2 [%falseResult_26, %trueResult_87] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<f32>, <f32>] to <f32>
    %78 = mux %80#3 [%falseResult_28, %trueResult_89] {handshake.bb = 5 : ui32, handshake.name = "mux11"} : <i1>, [<f32>, <f32>] to <f32>
    %79 = mux %80#0 [%falseResult_30, %trueResult_91] {handshake.bb = 5 : ui32, handshake.name = "mux12"} : <i1>, [<i3>, <i3>] to <i3>
    %result_35, %index_36 = control_merge [%falseResult_32, %trueResult_93]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %80:4 = fork [4] %index_36 {handshake.bb = 5 : ui32, handshake.name = "fork16"} : <i1>
    %81:3 = lazy_fork [3] %result_35 {handshake.bb = 5 : ui32, handshake.name = "lazy_fork2"} : <>
    %addressResult_37, %dataResult_38 = load[%76#2] %1#0 {handshake.bb = 5 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load6"} : <i5>, <f32>, <i5>, <f32>
    %82 = constant %81#2 {handshake.bb = 5 : ui32, handshake.name = "constant11", value = false} : <>, <i1>
    %83 = br %82 {handshake.bb = 5 : ui32, handshake.name = "br16"} : <i1>
    %84 = extui %83 {handshake.bb = 6 : ui32, handshake.name = "extui29"} : <i1> to <i5>
    %85 = br %dataResult_38 {handshake.bb = 5 : ui32, handshake.name = "br17"} : <f32>
    %86 = br %77 {handshake.bb = 5 : ui32, handshake.name = "br18"} : <f32>
    %87 = br %78 {handshake.bb = 5 : ui32, handshake.name = "br19"} : <f32>
    %88 = br %79 {handshake.bb = 5 : ui32, handshake.name = "br20"} : <i3>
    %89 = br %76#3 {handshake.bb = 5 : ui32, handshake.name = "br21"} : <i5>
    %90 = br %76#0 {handshake.bb = 5 : ui32, handshake.name = "br22"} : <i5>
    %91 = br %76#1 {handshake.bb = 5 : ui32, handshake.name = "br23"} : <i5>
    %92 = br %81#1 {handshake.bb = 5 : ui32, handshake.name = "br24"} : <>
    %93 = mux %109#4 [%84, %trueResult_47] {handshake.bb = 6 : ui32, handshake.name = "mux13"} : <i1>, [<i5>, <i5>] to <i5>
    %94:3 = fork [3] %93 {handshake.bb = 6 : ui32, handshake.name = "fork17"} : <i5>
    %95 = extui %94#0 {handshake.bb = 6 : ui32, handshake.name = "extui30"} : <i5> to <i10>
    %96 = extui %94#2 {handshake.bb = 6 : ui32, handshake.name = "extui31"} : <i5> to <i6>
    %97 = constant %112 {handshake.bb = 6 : ui32, handshake.name = "constant12", value = 1 : i6} : <>, <i6>
    %98 = mux %109#5 [%85, %trueResult_49] {handshake.bb = 6 : ui32, handshake.name = "mux14"} : <i1>, [<f32>, <f32>] to <f32>
    %99 = mux %109#6 [%86, %trueResult_51] {handshake.bb = 6 : ui32, handshake.name = "mux15"} : <i1>, [<f32>, <f32>] to <f32>
    %100 = mux %109#7 [%87, %trueResult_53] {handshake.bb = 6 : ui32, handshake.name = "mux16"} : <i1>, [<f32>, <f32>] to <f32>
    %101 = mux %109#0 [%88, %trueResult_55] {handshake.bb = 6 : ui32, handshake.name = "mux17"} : <i1>, [<i3>, <i3>] to <i3>
    %102 = mux %109#3 [%89, %trueResult_57] {handshake.bb = 6 : ui32, handshake.name = "mux18"} : <i1>, [<i5>, <i5>] to <i5>
    %103 = mux %109#1 [%90, %trueResult_59] {handshake.bb = 6 : ui32, handshake.name = "mux19"} : <i1>, [<i5>, <i5>] to <i5>
    %104:2 = fork [2] %103 {handshake.bb = 6 : ui32, handshake.name = "fork18"} : <i5>
    %105 = extui %104#1 {handshake.bb = 6 : ui32, handshake.name = "extui32"} : <i5> to <i64>
    %106:4 = fork [4] %105 {handshake.bb = 6 : ui32, handshake.name = "fork19"} : <i64>
    %107 = mux %109#2 [%91, %trueResult_61] {handshake.bb = 6 : ui32, handshake.name = "mux20"} : <i1>, [<i5>, <i5>] to <i5>
    %108:2 = fork [2] %107 {handshake.bb = 6 : ui32, handshake.name = "fork20"} : <i5>
    %result_39, %index_40 = control_merge [%92, %trueResult_63]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %109:8 = fork [8] %index_40 {handshake.bb = 6 : ui32, handshake.name = "fork21"} : <i1>
    %110:3 = lazy_fork [3] %result_39 {handshake.bb = 6 : ui32, handshake.name = "lazy_fork3"} : <>
    %111 = source {handshake.bb = 6 : ui32, handshake.name = "source5"} : <>
    %112 = source {handshake.bb = 6 : ui32, handshake.name = "source6"} : <>
    %113 = source {handshake.bb = 6 : ui32, handshake.name = "source7"} : <>
    %114 = constant %113 {handshake.bb = 6 : ui32, handshake.name = "constant29", value = 4 : i64} : <>, <i64>
    %115 = source {handshake.bb = 6 : ui32, handshake.name = "source8"} : <>
    %116 = constant %115 {handshake.bb = 6 : ui32, handshake.name = "constant30", value = 3 : i64} : <>, <i64>
    %117 = source {handshake.bb = 6 : ui32, handshake.name = "source9"} : <>
    %118 = constant %117 {handshake.bb = 6 : ui32, handshake.name = "constant31", value = 2 : i64} : <>, <i64>
    %119 = source {handshake.bb = 6 : ui32, handshake.name = "source10"} : <>
    %120 = constant %119 {handshake.bb = 6 : ui32, handshake.name = "constant32", value = 1 : i64} : <>, <i64>
    %121 = shli %106#0, %120 {handshake.bb = 6 : ui32, handshake.name = "shli0"} : <i64>
    %122 = trunci %121 {handshake.bb = 6 : ui32, handshake.name = "trunci2"} : <i64> to <i10>
    %123 = shli %106#1, %118 {handshake.bb = 6 : ui32, handshake.name = "shli1"} : <i64>
    %124 = trunci %123 {handshake.bb = 6 : ui32, handshake.name = "trunci3"} : <i64> to <i10>
    %125 = addi %122, %124 {handshake.bb = 6 : ui32, handshake.name = "addi7"} : <i10>
    %126 = shli %106#2, %116 {handshake.bb = 6 : ui32, handshake.name = "shli2"} : <i64>
    %127 = trunci %126 {handshake.bb = 6 : ui32, handshake.name = "trunci4"} : <i64> to <i10>
    %128 = shli %106#3, %114 {handshake.bb = 6 : ui32, handshake.name = "shli3"} : <i64>
    %129 = trunci %128 {handshake.bb = 6 : ui32, handshake.name = "trunci5"} : <i64> to <i10>
    %130 = addi %127, %129 {handshake.bb = 6 : ui32, handshake.name = "addi8"} : <i10>
    %131 = addi %125, %130 {handshake.bb = 6 : ui32, handshake.name = "addi9"} : <i10>
    %132 = addi %131, %95 {handshake.bb = 6 : ui32, handshake.name = "addi2"} : <i10>
    %addressResult_41, %dataResult_42 = load[%132] %outputs {handshake.bb = 6 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load7"} : <i10>, <f32>, <i10>, <f32>
    %addressResult_43, %dataResult_44 = load[%94#1] %2#0 {handshake.bb = 6 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load8"} : <i5>, <f32>, <i5>, <f32>
    %133 = mulf %dataResult_42, %dataResult_44 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "mulf1"} : <f32>
    %134 = addf %98, %133 {fastmath = #arith.fastmath<none>, handshake.bb = 6 : ui32, handshake.name = "addf0"} : <f32>
    %135:2 = fork [2] %134 {handshake.bb = 6 : ui32, handshake.name = "fork22"} : <f32>
    %addressResult_45, %dataResult_46 = store[%108#0] %135#0 {handshake.bb = 6 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load13", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store9"} : <i5>, <f32>, <i5>, <f32>
    %136 = addi %96, %97 {handshake.bb = 6 : ui32, handshake.name = "addi3"} : <i6>
    %137:2 = fork [2] %136 {handshake.bb = 6 : ui32, handshake.name = "fork23"} : <i6>
    %138 = trunci %137#0 {handshake.bb = 6 : ui32, handshake.name = "trunci6"} : <i6> to <i5>
    %139 = constant %111 {handshake.bb = 6 : ui32, handshake.name = "constant13", value = 30 : i6} : <>, <i6>
    %140 = cmpi ult, %137#1, %139 {handshake.bb = 6 : ui32, handshake.name = "cmpi2"} : <i6>
    %141:9 = fork [9] %140 {handshake.bb = 6 : ui32, handshake.name = "fork24"} : <i1>
    %trueResult_47, %falseResult_48 = cond_br %141#0, %138 {handshake.bb = 6 : ui32, handshake.name = "cond_br15"} : <i1>, <i5>
    sink %falseResult_48 {handshake.name = "sink4"} : <i5>
    %trueResult_49, %falseResult_50 = cond_br %141#5, %135#1 {handshake.bb = 6 : ui32, handshake.name = "cond_br16"} : <i1>, <f32>
    sink %falseResult_50 {handshake.name = "sink5"} : <f32>
    %trueResult_51, %falseResult_52 = cond_br %141#6, %99 {handshake.bb = 6 : ui32, handshake.name = "cond_br17"} : <i1>, <f32>
    %trueResult_53, %falseResult_54 = cond_br %141#7, %100 {handshake.bb = 6 : ui32, handshake.name = "cond_br18"} : <i1>, <f32>
    %trueResult_55, %falseResult_56 = cond_br %141#1, %101 {handshake.bb = 6 : ui32, handshake.name = "cond_br19"} : <i1>, <i3>
    %trueResult_57, %falseResult_58 = cond_br %141#4, %102 {handshake.bb = 6 : ui32, handshake.name = "cond_br20"} : <i1>, <i5>
    %trueResult_59, %falseResult_60 = cond_br %141#2, %104#0 {handshake.bb = 6 : ui32, handshake.name = "cond_br21"} : <i1>, <i5>
    sink %falseResult_60 {handshake.name = "sink6"} : <i5>
    %trueResult_61, %falseResult_62 = cond_br %141#3, %108#1 {handshake.bb = 6 : ui32, handshake.name = "cond_br22"} : <i1>, <i5>
    sink %falseResult_62 {handshake.name = "sink7"} : <i5>
    %trueResult_63, %falseResult_64 = cond_br %141#8, %110#1 {handshake.bb = 6 : ui32, handshake.name = "cond_br23"} : <i1>, <>
    %142 = merge %falseResult_52 {handshake.bb = 7 : ui32, handshake.name = "merge1"} : <f32>
    %143:3 = fork [3] %142 {handshake.bb = 7 : ui32, handshake.name = "fork25"} : <f32>
    %144 = merge %falseResult_54 {handshake.bb = 7 : ui32, handshake.name = "merge2"} : <f32>
    %145:3 = fork [3] %144 {handshake.bb = 7 : ui32, handshake.name = "fork26"} : <f32>
    %146 = merge %falseResult_56 {handshake.bb = 7 : ui32, handshake.name = "merge3"} : <i3>
    %147 = merge %falseResult_58 {handshake.bb = 7 : ui32, handshake.name = "merge4"} : <i5>
    %148:10 = fork [10] %147 {handshake.bb = 7 : ui32, handshake.name = "fork27"} : <i5>
    %149 = extui %148#9 {handshake.bb = 7 : ui32, handshake.name = "extui33"} : <i5> to <i6>
    %150 = constant %160 {handshake.bb = 7 : ui32, handshake.name = "constant14", value = 1 : i6} : <>, <i6>
    %result_65, %index_66 = control_merge [%falseResult_64]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    sink %index_66 {handshake.name = "sink8"} : <i1>
    %151:6 = lazy_fork [6] %result_65 {handshake.bb = 7 : ui32, handshake.name = "lazy_fork4"} : <>
    %152 = source {handshake.bb = 7 : ui32, handshake.name = "source11"} : <>
    %153 = constant %152 {handshake.bb = 7 : ui32, handshake.name = "constant33", value = 1.000000e-01 : f32} : <>, <f32>
    %154 = source {handshake.bb = 7 : ui32, handshake.name = "source12"} : <>
    %155 = constant %154 {handshake.bb = 7 : ui32, handshake.name = "constant34", value = 1.000000e+01 : f32} : <>, <f32>
    %156 = source {handshake.bb = 7 : ui32, handshake.name = "source13"} : <>
    %157 = constant %156 {handshake.bb = 7 : ui32, handshake.name = "constant35", value = -6.000000e-01 : f32} : <>, <f32>
    %158:2 = fork [2] %157 {handshake.bb = 7 : ui32, handshake.name = "fork28"} : <f32>
    %159 = source {handshake.bb = 7 : ui32, handshake.name = "source14"} : <>
    %160 = source {handshake.bb = 7 : ui32, handshake.name = "source15"} : <>
    %addressResult_67, %dataResult_68 = load[%148#8] %1#1 {handshake.bb = 7 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 3>, handshake.name = "load10"} : <i5>, <f32>, <i5>, <f32>
    %addressResult_69, %dataResult_70 = load[%148#7] %5#0 {handshake.bb = 7 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load11"} : <i5>, <f32>, <i5>, <f32>
    %161 = mulf %dataResult_70, %158#1 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "mulf2"} : <f32>
    %162 = addf %dataResult_68, %161 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "addf1"} : <f32>
    %addressResult_71, %dataResult_72 = store[%148#6] %162 {handshake.bb = 7 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load11", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load19", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store12"} : <i5>, <f32>, <i5>, <f32>
    %addressResult_73, %dataResult_74 = load[%148#5] %1#2 {handshake.bb = 7 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 3>, handshake.name = "load13"} : <i5>, <f32>, <i5>, <f32>
    %addressResult_75, %dataResult_76 = load[%148#4] %4#0 {handshake.bb = 7 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load14"} : <i5>, <f32>, <i5>, <f32>
    %163 = mulf %dataResult_76, %158#0 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "mulf3"} : <f32>
    %164 = addf %dataResult_74, %163 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "addf2"} : <f32>
    %165:2 = fork [2] %164 {handshake.bb = 7 : ui32, handshake.name = "fork29"} : <f32>
    %addressResult_77, %dataResult_78 = load[%148#3] %3#0 {handshake.bb = 7 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load15"} : <i5>, <f32>, <i5>, <f32>
    %166 = mulf %dataResult_78, %155 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "mulf4"} : <f32>
    %167 = addf %165#1, %166 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "addf3"} : <f32>
    %168:3 = fork [3] %167 {handshake.bb = 7 : ui32, handshake.name = "fork30"} : <f32>
    %169 = cmpf olt, %168#2, %145#2 {handshake.bb = 7 : ui32, handshake.name = "cmpf0"} : <f32>
    %170 = cmpf ogt, %168#1, %143#2 {handshake.bb = 7 : ui32, handshake.name = "cmpf1"} : <f32>
    %171 = select %170[%143#1, %168#0] {handshake.bb = 7 : ui32, handshake.name = "select0"} : <i1>, <f32>
    %172 = select %169[%145#1, %171] {handshake.bb = 7 : ui32, handshake.name = "select1"} : <i1>, <f32>
    %173:2 = fork [2] %172 {handshake.bb = 7 : ui32, handshake.name = "fork31"} : <f32>
    %addressResult_79, %dataResult_80 = store[%148#2] %173#0 {handshake.bb = 7 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load20", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store16"} : <i5>, <f32>, <i5>, <f32>
    %addressResult_81, %dataResult_82 = load[%148#1] %3#1 {handshake.bb = 7 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load17"} : <i5>, <f32>, <i5>, <f32>
    %174 = subf %165#0, %173#1 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "subf0"} : <f32>
    %175 = mulf %174, %153 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "mulf5"} : <f32>
    %176 = addf %dataResult_82, %175 {fastmath = #arith.fastmath<none>, handshake.bb = 7 : ui32, handshake.name = "addf4"} : <f32>
    %addressResult_83, %dataResult_84 = store[%148#0] %176 {handshake.bb = 7 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load17", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load21", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store18"} : <i5>, <f32>, <i5>, <f32>
    %177 = addi %149, %150 {handshake.bb = 7 : ui32, handshake.name = "addi4"} : <i6>
    %178:2 = fork [2] %177 {handshake.bb = 7 : ui32, handshake.name = "fork32"} : <i6>
    %179 = trunci %178#0 {handshake.bb = 7 : ui32, handshake.name = "trunci7"} : <i6> to <i5>
    %180 = constant %159 {handshake.bb = 7 : ui32, handshake.name = "constant15", value = 30 : i6} : <>, <i6>
    %181 = cmpi ult, %178#1, %180 {handshake.bb = 7 : ui32, handshake.name = "cmpi3"} : <i6>
    %182:6 = fork [6] %181 {handshake.bb = 7 : ui32, handshake.name = "fork33"} : <i1>
    %trueResult_85, %falseResult_86 = cond_br %182#0, %179 {handshake.bb = 7 : ui32, handshake.name = "cond_br24"} : <i1>, <i5>
    sink %falseResult_86 {handshake.name = "sink9"} : <i5>
    %trueResult_87, %falseResult_88 = cond_br %182#2, %143#0 {handshake.bb = 7 : ui32, handshake.name = "cond_br25"} : <i1>, <f32>
    %trueResult_89, %falseResult_90 = cond_br %182#3, %145#0 {handshake.bb = 7 : ui32, handshake.name = "cond_br26"} : <i1>, <f32>
    %trueResult_91, %falseResult_92 = cond_br %182#1, %146 {handshake.bb = 7 : ui32, handshake.name = "cond_br27"} : <i1>, <i3>
    %trueResult_93, %falseResult_94 = cond_br %182#4, %151#1 {handshake.bb = 7 : ui32, handshake.name = "cond_br28"} : <i1>, <>
    %183 = constant %151#5 {handshake.bb = 7 : ui32, handshake.name = "constant46", value = false} : <>, <i1>
    %trueResult_95, %falseResult_96 = cond_br %182#5, %183 {handshake.bb = 7 : ui32, handshake.name = "cond_br29"} : <i1>, <i1>
    sink %trueResult_95 {handshake.name = "sink10"} : <i1>
    %184 = extui %falseResult_96 {handshake.bb = 8 : ui32, handshake.name = "extui34"} : <i1> to <i5>
    %185 = mux %192#1 [%184, %trueResult_107] {handshake.bb = 8 : ui32, handshake.name = "mux21"} : <i1>, [<i5>, <i5>] to <i5>
    %186:5 = fork [5] %185 {handshake.bb = 8 : ui32, handshake.name = "fork34"} : <i5>
    %187 = extui %186#4 {handshake.bb = 8 : ui32, handshake.name = "extui35"} : <i5> to <i6>
    %188 = constant %197 {handshake.bb = 8 : ui32, handshake.name = "constant47", value = 1 : i6} : <>, <i6>
    %189 = mux %192#2 [%falseResult_88, %trueResult_109] {handshake.bb = 8 : ui32, handshake.name = "mux22"} : <i1>, [<f32>, <f32>] to <f32>
    %190 = mux %192#3 [%falseResult_90, %trueResult_111] {handshake.bb = 8 : ui32, handshake.name = "mux23"} : <i1>, [<f32>, <f32>] to <f32>
    %191 = mux %192#0 [%falseResult_92, %trueResult_113] {handshake.bb = 8 : ui32, handshake.name = "mux24"} : <i1>, [<i3>, <i3>] to <i3>
    %result_97, %index_98 = control_merge [%falseResult_94, %trueResult_115]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>] to <>, <i1>
    %192:4 = fork [4] %index_98 {handshake.bb = 8 : ui32, handshake.name = "fork35"} : <i1>
    %193:5 = lazy_fork [5] %result_97 {handshake.bb = 8 : ui32, handshake.name = "lazy_fork5"} : <>
    %194 = source {handshake.bb = 8 : ui32, handshake.name = "source16"} : <>
    %195 = constant %194 {handshake.bb = 8 : ui32, handshake.name = "constant39", value = 1.000000e-01 : f32} : <>, <f32>
    %196 = source {handshake.bb = 8 : ui32, handshake.name = "source17"} : <>
    %197 = source {handshake.bb = 8 : ui32, handshake.name = "source18"} : <>
    %addressResult_99, %dataResult_100 = load[%186#3] %5#1 {handshake.bb = 8 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load19"} : <i5>, <f32>, <i5>, <f32>
    %addressResult_101, %dataResult_102 = load[%186#2] %4#1 {handshake.bb = 8 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load20"} : <i5>, <f32>, <i5>, <f32>
    %198 = mulf %dataResult_102, %195 {fastmath = #arith.fastmath<none>, handshake.bb = 8 : ui32, handshake.name = "mulf6"} : <f32>
    %199 = addf %dataResult_100, %198 {fastmath = #arith.fastmath<none>, handshake.bb = 8 : ui32, handshake.name = "addf5"} : <f32>
    %addressResult_103, %dataResult_104 = load[%186#1] %3#2 {handshake.bb = 8 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load21"} : <i5>, <f32>, <i5>, <f32>
    %200 = subf %199, %dataResult_104 {fastmath = #arith.fastmath<none>, handshake.bb = 8 : ui32, handshake.name = "subf1"} : <f32>
    %addressResult_105, %dataResult_106 = store[%186#0] %200 {handshake.bb = 8 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load23", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load25", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store22"} : <i5>, <f32>, <i5>, <f32>
    %201 = addi %187, %188 {handshake.bb = 8 : ui32, handshake.name = "addi5"} : <i6>
    %202:2 = fork [2] %201 {handshake.bb = 8 : ui32, handshake.name = "fork36"} : <i6>
    %203 = trunci %202#0 {handshake.bb = 8 : ui32, handshake.name = "trunci8"} : <i6> to <i5>
    %204 = constant %196 {handshake.bb = 8 : ui32, handshake.name = "constant48", value = 30 : i6} : <>, <i6>
    %205 = cmpi ult, %202#1, %204 {handshake.bb = 8 : ui32, handshake.name = "cmpi4"} : <i6>
    %206:5 = fork [5] %205 {handshake.bb = 8 : ui32, handshake.name = "fork37"} : <i1>
    %trueResult_107, %falseResult_108 = cond_br %206#0, %203 {handshake.bb = 8 : ui32, handshake.name = "cond_br30"} : <i1>, <i5>
    sink %falseResult_108 {handshake.name = "sink11"} : <i5>
    %trueResult_109, %falseResult_110 = cond_br %206#2, %189 {handshake.bb = 8 : ui32, handshake.name = "cond_br31"} : <i1>, <f32>
    %trueResult_111, %falseResult_112 = cond_br %206#3, %190 {handshake.bb = 8 : ui32, handshake.name = "cond_br32"} : <i1>, <f32>
    %trueResult_113, %falseResult_114 = cond_br %206#1, %191 {handshake.bb = 8 : ui32, handshake.name = "cond_br33"} : <i1>, <i3>
    %trueResult_115, %falseResult_116 = cond_br %206#4, %193#1 {handshake.bb = 8 : ui32, handshake.name = "cond_br34"} : <i1>, <>
    %207 = merge %falseResult_110 {handshake.bb = 9 : ui32, handshake.name = "merge5"} : <f32>
    %208 = merge %falseResult_112 {handshake.bb = 9 : ui32, handshake.name = "merge6"} : <f32>
    %209 = merge %falseResult_114 {handshake.bb = 9 : ui32, handshake.name = "merge7"} : <i3>
    %210 = extui %209 {handshake.bb = 9 : ui32, handshake.name = "extui36"} : <i3> to <i4>
    %211 = constant %213 {handshake.bb = 9 : ui32, handshake.name = "constant49", value = 1 : i4} : <>, <i4>
    %result_117, %index_118 = control_merge [%falseResult_116]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    sink %index_118 {handshake.name = "sink12"} : <i1>
    %212 = source {handshake.bb = 9 : ui32, handshake.name = "source19"} : <>
    %213 = source {handshake.bb = 9 : ui32, handshake.name = "source20"} : <>
    %214 = addi %210, %211 {handshake.bb = 9 : ui32, handshake.name = "addi6"} : <i4>
    %215:2 = fork [2] %214 {handshake.bb = 9 : ui32, handshake.name = "fork38"} : <i4>
    %216 = trunci %215#0 {handshake.bb = 9 : ui32, handshake.name = "trunci9"} : <i4> to <i3>
    %217 = constant %212 {handshake.bb = 9 : ui32, handshake.name = "constant50", value = 7 : i4} : <>, <i4>
    %218 = cmpi ult, %215#1, %217 {handshake.bb = 9 : ui32, handshake.name = "cmpi5"} : <i4>
    %219:4 = fork [4] %218 {handshake.bb = 9 : ui32, handshake.name = "fork39"} : <i1>
    %trueResult_119, %falseResult_120 = cond_br %219#0, %216 {handshake.bb = 9 : ui32, handshake.name = "cond_br35"} : <i1>, <i3>
    sink %falseResult_120 {handshake.name = "sink13"} : <i3>
    %trueResult_121, %falseResult_122 = cond_br %219#1, %207 {handshake.bb = 9 : ui32, handshake.name = "cond_br36"} : <i1>, <f32>
    sink %falseResult_122 {handshake.name = "sink14"} : <f32>
    %trueResult_123, %falseResult_124 = cond_br %219#2, %208 {handshake.bb = 9 : ui32, handshake.name = "cond_br37"} : <i1>, <f32>
    sink %falseResult_124 {handshake.name = "sink15"} : <f32>
    %trueResult_125, %falseResult_126 = cond_br %219#3, %result_117 {handshake.bb = 9 : ui32, handshake.name = "cond_br38"} : <i1>, <>
    %result_127, %index_128 = control_merge [%falseResult_126]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>] to <>, <i1>
    sink %index_128 {handshake.name = "sink16"} : <i1>
    %220:14 = fork [14] %result_127 {handshake.bb = 10 : ui32, handshake.name = "fork40"} : <>
    %221 = constant %220#13 {handshake.bb = 10 : ui32, handshake.name = "constant2", value = 2 : i32} : <>, <i32>
    %222 = constant %220#0 {handshake.bb = 10 : ui32, handshake.name = "constant51", value = 0 : i5} : <>, <i5>
    %addressResult_129, %dataResult_130 = load[%222] %2#1 {handshake.bb = 10 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 3>, handshake.name = "load23"} : <i5>, <f32>, <i5>, <f32>
    %223 = constant %220#3 {handshake.bb = 10 : ui32, handshake.name = "constant52", value = false} : <>, <i1>
    %addressResult_131, %dataResult_132 = store[%223] %dataResult_130 {handshake.bb = 10 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store24"} : <i1>, <f32>, <i1>, <f32>
    %224 = constant %220#1 {handshake.bb = 10 : ui32, handshake.name = "constant53", value = 1 : i5} : <>, <i5>
    %addressResult_133, %dataResult_134 = load[%224] %2#2 {handshake.bb = 10 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 3>, handshake.name = "load25"} : <i5>, <f32>, <i5>, <f32>
    %225 = constant %220#2 {handshake.bb = 10 : ui32, handshake.name = "constant54", value = true} : <>, <i1>
    %addressResult_135, %dataResult_136 = store[%225] %dataResult_134 {handshake.bb = 10 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store26"} : <i1>, <f32>, <i1>, <f32>
    end {handshake.bb = 10 : ui32, handshake.name = "end0"} %memEnd_2, %memEnd_0, %memEnd, %5#2, %4#2, %3#3, %2#3, %1#3, %0#1 : <>, <>, <>, <>, <>, <>, <>, <>, <>
  }
}

