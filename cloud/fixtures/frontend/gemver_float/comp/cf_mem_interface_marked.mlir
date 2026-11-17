module {
  func.func @gemver_float(%arg0: f32 {handshake.arg_name = "alpha"}, %arg1: f32 {handshake.arg_name = "beta"}, %arg2: memref<100xf32> {handshake.arg_name = "A"}, %arg3: memref<10xf32> {handshake.arg_name = "u1"}, %arg4: memref<10xf32> {handshake.arg_name = "v1"}, %arg5: memref<10xf32> {handshake.arg_name = "u2"}, %arg6: memref<10xf32> {handshake.arg_name = "v2"}, %arg7: memref<10xf32> {handshake.arg_name = "w"}, %arg8: memref<10xf32> {handshake.arg_name = "x"}, %arg9: memref<10xf32> {handshake.arg_name = "y"}, %arg10: memref<10xf32> {handshake.arg_name = "z"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant6"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %3 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %4 = arith.extui %0 {handshake.name = "extui3"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%5: i32):  // 2 preds: ^bb1, ^bb2
    %c10_i32 = arith.constant {handshake.name = "constant7"} 10 : i32
    %c1_i32 = arith.constant {handshake.name = "constant8"} 1 : i32
    %c3_i64 = arith.constant {handshake.name = "constant9"} 3 : i64
    %c1_i64 = arith.constant {handshake.name = "constant10"} 1 : i64
    %6 = arith.extui %5 {handshake.name = "extui4"} : i32 to i64
    %7 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %8 = arith.shli %1, %c3_i64 {handshake.name = "shli1"} : i64
    %9 = arith.addi %7, %8 {handshake.name = "addi11"} : i64
    %10 = arith.addi %9, %6 {handshake.name = "addi0"} : i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast0"} : i64 to index
    %12 = memref.load %arg2[%11] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<100xf32>
    %13 = arith.index_cast %2 {handshake.name = "index_cast1"} : i64 to index
    %14 = memref.load %arg3[%13] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<10xf32>
    %15 = arith.extui %5 {handshake.name = "extui5"} : i32 to i64
    %16 = arith.index_cast %15 {handshake.name = "index_cast2"} : i64 to index
    %17 = memref.load %arg4[%16] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load2"} : memref<10xf32>
    %18 = arith.mulf %14, %17 {handshake.name = "mulf0"} : f32
    %19 = arith.addf %12, %18 {handshake.name = "addf0"} : f32
    %20 = arith.index_cast %3 {handshake.name = "index_cast3"} : i64 to index
    %21 = memref.load %arg5[%20] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : memref<10xf32>
    %22 = arith.extui %5 {handshake.name = "extui6"} : i32 to i64
    %23 = arith.index_cast %22 {handshake.name = "index_cast4"} : i64 to index
    %24 = memref.load %arg6[%23] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load4"} : memref<10xf32>
    %25 = arith.mulf %21, %24 {handshake.name = "mulf1"} : f32
    %26 = arith.addf %19, %25 {handshake.name = "addf1"} : f32
    %27 = arith.extui %5 {handshake.name = "extui7"} : i32 to i64
    %28 = arith.shli %4, %c1_i64 {handshake.name = "shli2"} : i64
    %29 = arith.shli %4, %c3_i64 {handshake.name = "shli3"} : i64
    %30 = arith.addi %28, %29 {handshake.name = "addi12"} : i64
    %31 = arith.addi %30, %27 {handshake.name = "addi1"} : i64
    %32 = arith.index_cast %31 {handshake.name = "index_cast5"} : i64 to index
    memref.store %26, %arg2[%32] {handshake.deps = #handshake<deps[{dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store5"} : memref<100xf32>
    %33 = arith.addi %5, %c1_i32 {handshake.name = "addi2"} : i32
    %34 = arith.cmpi ult, %33, %c10_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %34, ^bb2(%33 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c10_i32_1 = arith.constant {handshake.name = "constant11"} 10 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant12"} 1 : i32
    %c0_i32_3 = arith.constant {handshake.name = "constant13"} 0 : i32
    %35 = arith.addi %0, %c1_i32_2 {handshake.name = "addi3"} : i32
    %36 = arith.cmpi ult, %35, %c10_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %36, ^bb1(%35 : i32), ^bb4(%c0_i32_3 : i32) {handshake.name = "cond_br1"}
  ^bb4(%37: i32):  // 2 preds: ^bb3, ^bb6
    %c0_i32_4 = arith.constant {handshake.name = "constant14"} 0 : i32
    %38 = arith.extui %37 {handshake.name = "extui8"} : i32 to i64
    %39 = arith.index_cast %38 {handshake.name = "index_cast6"} : i64 to index
    %40 = memref.load %arg8[%39] {handshake.mem_interface = #handshake.mem_interface<LSQ: 3>, handshake.name = "load6"} : memref<10xf32>
    %41 = arith.extui %37 {handshake.name = "extui9"} : i32 to i64
    cf.br ^bb5(%40, %c0_i32_4 : f32, i32) {handshake.name = "br2"}
  ^bb5(%42: f32, %43: i32):  // 2 preds: ^bb4, ^bb5
    %c10_i32_5 = arith.constant {handshake.name = "constant15"} 10 : i32
    %c1_i32_6 = arith.constant {handshake.name = "constant16"} 1 : i32
    %c3_i64_7 = arith.constant {handshake.name = "constant17"} 3 : i64
    %c1_i64_8 = arith.constant {handshake.name = "constant18"} 1 : i64
    %44 = arith.extui %43 {handshake.name = "extui10"} : i32 to i64
    %45 = arith.shli %44, %c1_i64_8 {handshake.name = "shli4"} : i64
    %46 = arith.shli %44, %c3_i64_7 {handshake.name = "shli5"} : i64
    %47 = arith.addi %45, %46 {handshake.name = "addi13"} : i64
    %48 = arith.addi %47, %41 {handshake.name = "addi4"} : i64
    %49 = arith.index_cast %48 {handshake.name = "index_cast7"} : i64 to index
    %50 = memref.load %arg2[%49] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load7"} : memref<100xf32>
    %51 = arith.mulf %50, %arg1 {handshake.name = "mulf2"} : f32
    %52 = arith.extui %43 {handshake.name = "extui11"} : i32 to i64
    %53 = arith.index_cast %52 {handshake.name = "index_cast8"} : i64 to index
    %54 = memref.load %arg9[%53] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load8"} : memref<10xf32>
    %55 = arith.mulf %51, %54 {handshake.name = "mulf3"} : f32
    %56 = arith.addf %42, %55 {handshake.name = "addf2"} : f32
    %57 = arith.addi %43, %c1_i32_6 {handshake.name = "addi5"} : i32
    %58 = arith.cmpi ult, %57, %c10_i32_5 {handshake.name = "cmpi2"} : i32
    cf.cond_br %58, ^bb5(%56, %57 : f32, i32), ^bb6(%56 : f32) {handshake.name = "cond_br2"}
  ^bb6(%59: f32):  // pred: ^bb5
    %c10_i32_9 = arith.constant {handshake.name = "constant19"} 10 : i32
    %c1_i32_10 = arith.constant {handshake.name = "constant20"} 1 : i32
    %c0_i32_11 = arith.constant {handshake.name = "constant21"} 0 : i32
    %60 = arith.extui %37 {handshake.name = "extui12"} : i32 to i64
    %61 = arith.index_cast %60 {handshake.name = "index_cast9"} : i64 to index
    memref.store %59, %arg8[%61] {handshake.deps = #handshake<deps[{dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store12", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store9"} : memref<10xf32>
    %62 = arith.addi %37, %c1_i32_10 {handshake.name = "addi6"} : i32
    %63 = arith.cmpi ult, %62, %c10_i32_9 {handshake.name = "cmpi3"} : i32
    cf.cond_br %63, ^bb4(%62 : i32), ^bb7(%c0_i32_11 : i32) {handshake.name = "cond_br3"}
  ^bb7(%64: i32):  // 2 preds: ^bb6, ^bb7
    %c10_i32_12 = arith.constant {handshake.name = "constant22"} 10 : i32
    %c1_i32_13 = arith.constant {handshake.name = "constant23"} 1 : i32
    %c0_i32_14 = arith.constant {handshake.name = "constant24"} 0 : i32
    %65 = arith.extui %64 {handshake.name = "extui13"} : i32 to i64
    %66 = arith.index_cast %65 {handshake.name = "index_cast10"} : i64 to index
    %67 = memref.load %arg8[%66] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load10"} : memref<10xf32>
    %68 = arith.extui %64 {handshake.name = "extui14"} : i32 to i64
    %69 = arith.index_cast %68 {handshake.name = "index_cast11"} : i64 to index
    %70 = memref.load %arg10[%69] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load11"} : memref<10xf32>
    %71 = arith.addf %67, %70 {handshake.name = "addf3"} : f32
    %72 = arith.extui %64 {handshake.name = "extui15"} : i32 to i64
    %73 = arith.index_cast %72 {handshake.name = "index_cast12"} : i64 to index
    memref.store %71, %arg8[%73] {handshake.deps = #handshake<deps[{dstAccess : "store9", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load15", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store12"} : memref<10xf32>
    %74 = arith.addi %64, %c1_i32_13 {handshake.name = "addi7"} : i32
    %75 = arith.cmpi ult, %74, %c10_i32_12 {handshake.name = "cmpi4"} : i32
    cf.cond_br %75, ^bb7(%74 : i32), ^bb8(%c0_i32_14 : i32) {handshake.name = "cond_br4"}
  ^bb8(%76: i32):  // 2 preds: ^bb7, ^bb10
    %c0_i32_15 = arith.constant {handshake.name = "constant25"} 0 : i32
    %77 = arith.extui %76 {handshake.name = "extui16"} : i32 to i64
    %78 = arith.index_cast %77 {handshake.name = "index_cast13"} : i64 to index
    %79 = memref.load %arg7[%78] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load13"} : memref<10xf32>
    %80 = arith.extui %76 {handshake.name = "extui17"} : i32 to i64
    cf.br ^bb9(%79, %c0_i32_15 : f32, i32) {handshake.name = "br3"}
  ^bb9(%81: f32, %82: i32):  // 2 preds: ^bb8, ^bb9
    %c10_i32_16 = arith.constant {handshake.name = "constant26"} 10 : i32
    %c1_i32_17 = arith.constant {handshake.name = "constant27"} 1 : i32
    %c3_i64_18 = arith.constant {handshake.name = "constant28"} 3 : i64
    %c1_i64_19 = arith.constant {handshake.name = "constant29"} 1 : i64
    %83 = arith.extui %82 {handshake.name = "extui18"} : i32 to i64
    %84 = arith.shli %80, %c1_i64_19 {handshake.name = "shli6"} : i64
    %85 = arith.shli %80, %c3_i64_18 {handshake.name = "shli7"} : i64
    %86 = arith.addi %84, %85 {handshake.name = "addi14"} : i64
    %87 = arith.addi %86, %83 {handshake.name = "addi8"} : i64
    %88 = arith.index_cast %87 {handshake.name = "index_cast14"} : i64 to index
    %89 = memref.load %arg2[%88] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load14"} : memref<100xf32>
    %90 = arith.mulf %89, %arg0 {handshake.name = "mulf4"} : f32
    %91 = arith.extui %82 {handshake.name = "extui19"} : i32 to i64
    %92 = arith.index_cast %91 {handshake.name = "index_cast15"} : i64 to index
    %93 = memref.load %arg8[%92] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load15"} : memref<10xf32>
    %94 = arith.mulf %90, %93 {handshake.name = "mulf5"} : f32
    %95 = arith.addf %81, %94 {handshake.name = "addf4"} : f32
    %96 = arith.addi %82, %c1_i32_17 {handshake.name = "addi9"} : i32
    %97 = arith.cmpi ult, %96, %c10_i32_16 {handshake.name = "cmpi5"} : i32
    cf.cond_br %97, ^bb9(%95, %96 : f32, i32), ^bb10(%95 : f32) {handshake.name = "cond_br5"}
  ^bb10(%98: f32):  // pred: ^bb9
    %c10_i32_20 = arith.constant {handshake.name = "constant30"} 10 : i32
    %c1_i32_21 = arith.constant {handshake.name = "constant31"} 1 : i32
    %99 = arith.extui %76 {handshake.name = "extui20"} : i32 to i64
    %100 = arith.index_cast %99 {handshake.name = "index_cast16"} : i64 to index
    memref.store %98, %arg7[%100] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store16"} : memref<10xf32>
    %101 = arith.addi %76, %c1_i32_21 {handshake.name = "addi10"} : i32
    %102 = arith.cmpi ult, %101, %c10_i32_20 {handshake.name = "cmpi6"} : i32
    cf.cond_br %102, ^bb8(%101 : i32), ^bb11 {handshake.name = "cond_br6"}
  ^bb11:  // pred: ^bb10
    return {handshake.name = "return0"}
  }
}

