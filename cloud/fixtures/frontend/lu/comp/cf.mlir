module {
  memref.global "private" constant @__const.main.A : memref<9xf32> = dense<[1.000000e+00, 3.000000e+00, 5.000000e+00, 2.000000e+00, 4.000000e+00, 7.000000e+00, 1.000000e+00, 1.000000e+00, 0.000000e+00]> {alignment = 16 : i64}
  func.func @lu(%arg0: memref<9xf32>, %arg1: memref<9xf32>, %arg2: memref<9xf32>, %arg3: memref<9xf32>, %arg4: memref<9xf32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c3_i32 = arith.constant 3 : i32
    %cst = arith.constant 1.000000e+00 : f32
    %cst_0 = arith.constant 0.000000e+00 : f64
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%2: i32):  // 2 preds: ^bb1, ^bb2
    %3 = arith.cmpi eq, %0, %2 : i32
    %4 = arith.uitofp %3 : i1 to f32
    %5 = arith.extui %2 : i32 to i64
    %c3_i64 = arith.constant 3 : i64
    %6 = arith.muli %1, %c3_i64 : i64
    %7 = arith.addi %6, %5 : i64
    %8 = arith.index_cast %7 : i64 to index
    memref.store %4, %arg3[%8] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store0"} : memref<9xf32>
    %9 = arith.addi %2, %c1_i32 : i32
    %10 = arith.cmpi ult, %9, %c3_i32 : i32
    cf.cond_br %10, ^bb2(%9 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    %11 = arith.addi %0, %c1_i32 : i32
    %12 = arith.cmpi ult, %11, %c3_i32 : i32
    cf.cond_br %12, ^bb1(%11 : i32), ^bb4(%c0_i32 : i32)
  ^bb4(%13: i32):  // 2 preds: ^bb3, ^bb9
    cf.br ^bb5(%13, %13 : i32, i32)
  ^bb5(%14: i32, %15: i32):  // 2 preds: ^bb4, ^bb5
    %16 = arith.extui %15 : i32 to i64
    %17 = arith.extui %13 : i32 to i64
    %c3_i64_1 = arith.constant 3 : i64
    %18 = arith.muli %16, %c3_i64_1 : i64
    %19 = arith.addi %18, %17 : i64
    %20 = arith.index_cast %19 : i64 to index
    %21 = memref.load %arg0[%20] {handshake.name = "load1"} : memref<9xf32>
    %22 = math.absf %21 : f32
    %23 = arith.extsi %14 : i32 to i64
    %24 = arith.extui %13 : i32 to i64
    %c3_i64_2 = arith.constant 3 : i64
    %25 = arith.muli %23, %c3_i64_2 : i64
    %26 = arith.addi %25, %24 : i64
    %27 = arith.index_cast %26 : i64 to index
    %28 = memref.load %arg0[%27] {handshake.name = "load2"} : memref<9xf32>
    %29 = math.absf %28 : f32
    %30 = arith.cmpf ogt, %22, %29 : f32
    %31 = arith.select %30, %15, %14 : i32
    %32 = arith.addi %15, %c1_i32 : i32
    %33 = arith.cmpi ult, %32, %c3_i32 : i32
    cf.cond_br %33, ^bb5(%31, %32 : i32, i32), ^bb6(%31 : i32)
  ^bb6(%34: i32):  // pred: ^bb5
    %35 = arith.cmpi eq, %34, %13 : i32
    cf.cond_br %35, ^bb9, ^bb7
  ^bb7:  // pred: ^bb6
    %36 = arith.extui %13 : i32 to i64
    %37 = arith.extsi %34 : i32 to i64
    %38 = arith.extui %13 : i32 to i64
    %39 = arith.extsi %34 : i32 to i64
    cf.br ^bb8(%c0_i32 : i32)
  ^bb8(%40: i32):  // 2 preds: ^bb7, ^bb8
    %41 = arith.extui %40 : i32 to i64
    %c3_i64_3 = arith.constant 3 : i64
    %42 = arith.muli %36, %c3_i64_3 : i64
    %43 = arith.addi %42, %41 : i64
    %44 = arith.index_cast %43 : i64 to index
    %45 = memref.load %arg3[%44] {handshake.name = "load3"} : memref<9xf32>
    %46 = arith.fptosi %45 : f32 to i32
    %47 = arith.extui %40 : i32 to i64
    %c3_i64_4 = arith.constant 3 : i64
    %48 = arith.muli %37, %c3_i64_4 : i64
    %49 = arith.addi %48, %47 : i64
    %50 = arith.index_cast %49 : i64 to index
    %51 = memref.load %arg3[%50] {handshake.name = "load4"} : memref<9xf32>
    %52 = arith.extui %40 : i32 to i64
    %c3_i64_5 = arith.constant 3 : i64
    %53 = arith.muli %38, %c3_i64_5 : i64
    %54 = arith.addi %53, %52 : i64
    %55 = arith.index_cast %54 : i64 to index
    memref.store %51, %arg3[%55] {handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store6", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<9xf32>
    %56 = arith.sitofp %46 : i32 to f32
    %57 = arith.extui %40 : i32 to i64
    %c3_i64_6 = arith.constant 3 : i64
    %58 = arith.muli %39, %c3_i64_6 : i64
    %59 = arith.addi %58, %57 : i64
    %60 = arith.index_cast %59 : i64 to index
    memref.store %56, %arg3[%60] {handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store6"} : memref<9xf32>
    %61 = arith.addi %40, %c1_i32 : i32
    %62 = arith.cmpi ult, %61, %c3_i32 : i32
    cf.cond_br %62, ^bb8(%61 : i32), ^bb9
  ^bb9:  // 2 preds: ^bb6, ^bb8
    %63 = arith.addi %13, %c1_i32 : i32
    %64 = arith.cmpi ult, %63, %c3_i32 : i32
    cf.cond_br %64, ^bb4(%63 : i32), ^bb10(%c0_i32 : i32)
  ^bb10(%65: i32):  // 2 preds: ^bb9, ^bb14
    %66 = arith.extui %65 : i32 to i64
    %67 = arith.extui %65 : i32 to i64
    cf.br ^bb11(%c0_i32 : i32)
  ^bb11(%68: i32):  // 2 preds: ^bb10, ^bb13
    %69 = arith.extui %68 : i32 to i64
    %70 = arith.extui %68 : i32 to i64
    %c3_i64_7 = arith.constant 3 : i64
    %71 = arith.muli %67, %c3_i64_7 : i64
    %72 = arith.addi %71, %70 : i64
    %73 = arith.index_cast %72 : i64 to index
    %74 = memref.load %arg4[%73] {handshake.name = "load7"} : memref<9xf32>
    cf.br ^bb12(%c0_i32, %74 : i32, f32)
  ^bb12(%75: i32, %76: f32):  // 2 preds: ^bb11, ^bb12
    %77 = arith.extui %75 : i32 to i64
    %c3_i64_8 = arith.constant 3 : i64
    %78 = arith.muli %66, %c3_i64_8 : i64
    %79 = arith.addi %78, %77 : i64
    %80 = arith.index_cast %79 : i64 to index
    %81 = memref.load %arg3[%80] {handshake.name = "load8"} : memref<9xf32>
    %82 = arith.extui %75 : i32 to i64
    %c3_i64_9 = arith.constant 3 : i64
    %83 = arith.muli %82, %c3_i64_9 : i64
    %84 = arith.addi %83, %69 : i64
    %85 = arith.index_cast %84 : i64 to index
    %86 = memref.load %arg0[%85] {handshake.name = "load9"} : memref<9xf32>
    %87 = arith.mulf %81, %86 : f32
    %88 = arith.addf %76, %87 : f32
    %89 = arith.index_cast %72 : i64 to index
    memref.store %88, %arg4[%89] {handshake.deps = #handshake<deps[{dstAccess : "load14", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load18", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store10"} : memref<9xf32>
    %90 = arith.addi %75, %c1_i32 : i32
    %91 = arith.cmpi ult, %90, %c3_i32 : i32
    cf.cond_br %91, ^bb12(%90, %88 : i32, f32), ^bb13
  ^bb13:  // pred: ^bb12
    %92 = arith.addi %68, %c1_i32 : i32
    %93 = arith.cmpi ult, %92, %c3_i32 : i32
    cf.cond_br %93, ^bb11(%92 : i32), ^bb14
  ^bb14:  // pred: ^bb13
    %94 = arith.addi %65, %c1_i32 : i32
    %95 = arith.cmpi ult, %94, %c3_i32 : i32
    cf.cond_br %95, ^bb10(%94 : i32), ^bb15(%c0_i32 : i32)
  ^bb15(%96: i32):  // 2 preds: ^bb14, ^bb15
    %97 = arith.extui %96 : i32 to i64
    %98 = arith.extui %96 : i32 to i64
    %c3_i64_10 = arith.constant 3 : i64
    %99 = arith.muli %97, %c3_i64_10 : i64
    %100 = arith.addi %99, %98 : i64
    %101 = arith.index_cast %100 : i64 to index
    memref.store %cst, %arg1[%101] {handshake.deps = #handshake<deps[{dstAccess : "store20", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store11"} : memref<9xf32>
    %102 = arith.addi %96, %c1_i32 : i32
    %103 = arith.cmpi ult, %102, %c3_i32 : i32
    cf.cond_br %103, ^bb15(%102 : i32), ^bb16(%c0_i32 : i32)
  ^bb16(%104: i32):  // 2 preds: ^bb15, ^bb26
    cf.br ^bb17(%c0_i32 : i32)
  ^bb17(%105: i32):  // 2 preds: ^bb16, ^bb25
    %106 = arith.cmpi ugt, %105, %104 : i32
    cf.cond_br %106, ^bb21(%105 : i32), ^bb18
  ^bb18:  // pred: ^bb17
    %107 = arith.cmpi ult, %c0_i32, %105 : i32
    cf.cond_br %107, ^bb19(%c0_i32, %cst_0 : i32, f64), ^bb20(%cst_0 : f64)
  ^bb19(%108: i32, %109: f64):  // 2 preds: ^bb18, ^bb19
    %110 = arith.extui %105 : i32 to i64
    %111 = arith.extui %108 : i32 to i64
    %c3_i64_11 = arith.constant 3 : i64
    %112 = arith.muli %110, %c3_i64_11 : i64
    %113 = arith.addi %112, %111 : i64
    %114 = arith.index_cast %113 : i64 to index
    %115 = memref.load %arg1[%114] {handshake.name = "load12"} : memref<9xf32>
    %116 = arith.extui %108 : i32 to i64
    %117 = arith.extui %104 : i32 to i64
    %c3_i64_12 = arith.constant 3 : i64
    %118 = arith.muli %116, %c3_i64_12 : i64
    %119 = arith.addi %118, %117 : i64
    %120 = arith.index_cast %119 : i64 to index
    %121 = memref.load %arg2[%120] {handshake.name = "load13"} : memref<9xf32>
    %122 = arith.mulf %115, %121 : f32
    %123 = arith.extf %122 : f32 to f64
    %124 = arith.addf %109, %123 : f64
    %125 = arith.addi %108, %c1_i32 : i32
    %126 = arith.cmpi ult, %125, %105 : i32
    cf.cond_br %126, ^bb19(%125, %124 : i32, f64), ^bb20(%124 : f64)
  ^bb20(%127: f64):  // 2 preds: ^bb18, ^bb19
    %128 = arith.extui %105 : i32 to i64
    %129 = arith.extui %104 : i32 to i64
    %c3_i64_13 = arith.constant 3 : i64
    %130 = arith.muli %128, %c3_i64_13 : i64
    %131 = arith.addi %130, %129 : i64
    %132 = arith.index_cast %131 : i64 to index
    %133 = memref.load %arg4[%132] {handshake.name = "load14"} : memref<9xf32>
    %134 = arith.extf %133 : f32 to f64
    %135 = arith.subf %134, %127 : f64
    %136 = arith.truncf %135 : f64 to f32
    %137 = arith.extui %105 : i32 to i64
    %138 = arith.extui %104 : i32 to i64
    %c3_i64_14 = arith.constant 3 : i64
    %139 = arith.muli %137, %c3_i64_14 : i64
    %140 = arith.addi %139, %138 : i64
    %141 = arith.index_cast %140 : i64 to index
    memref.store %136, %arg2[%141] {handshake.deps = #handshake<deps[{dstAccess : "load13", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load17", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load19", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store15"} : memref<9xf32>
    cf.br ^bb21(%105 : i32)
  ^bb21(%142: i32):  // 2 preds: ^bb17, ^bb20
    %143 = arith.cmpi ult, %105, %104 : i32
    cf.cond_br %143, ^bb25, ^bb22
  ^bb22:  // pred: ^bb21
    %144 = arith.cmpi ult, %c0_i32, %104 : i32
    cf.cond_br %144, ^bb23(%c0_i32, %cst_0 : i32, f64), ^bb24(%cst_0 : f64)
  ^bb23(%145: i32, %146: f64):  // 2 preds: ^bb22, ^bb23
    %147 = arith.extui %142 : i32 to i64
    %148 = arith.extui %145 : i32 to i64
    %c3_i64_15 = arith.constant 3 : i64
    %149 = arith.muli %147, %c3_i64_15 : i64
    %150 = arith.addi %149, %148 : i64
    %151 = arith.index_cast %150 : i64 to index
    %152 = memref.load %arg1[%151] {handshake.name = "load16"} : memref<9xf32>
    %153 = arith.extui %145 : i32 to i64
    %154 = arith.extui %104 : i32 to i64
    %c3_i64_16 = arith.constant 3 : i64
    %155 = arith.muli %153, %c3_i64_16 : i64
    %156 = arith.addi %155, %154 : i64
    %157 = arith.index_cast %156 : i64 to index
    %158 = memref.load %arg2[%157] {handshake.name = "load17"} : memref<9xf32>
    %159 = arith.mulf %152, %158 : f32
    %160 = arith.extf %159 : f32 to f64
    %161 = arith.addf %146, %160 : f64
    %162 = arith.addi %145, %c1_i32 : i32
    %163 = arith.cmpi ult, %162, %104 : i32
    cf.cond_br %163, ^bb23(%162, %161 : i32, f64), ^bb24(%161 : f64)
  ^bb24(%164: f64):  // 2 preds: ^bb22, ^bb23
    %165 = arith.extui %142 : i32 to i64
    %166 = arith.extui %104 : i32 to i64
    %c3_i64_17 = arith.constant 3 : i64
    %167 = arith.muli %165, %c3_i64_17 : i64
    %168 = arith.addi %167, %166 : i64
    %169 = arith.index_cast %168 : i64 to index
    %170 = memref.load %arg4[%169] {handshake.name = "load18"} : memref<9xf32>
    %171 = arith.extf %170 : f32 to f64
    %172 = arith.subf %171, %164 : f64
    %173 = arith.extui %104 : i32 to i64
    %174 = arith.extui %104 : i32 to i64
    %c3_i64_18 = arith.constant 3 : i64
    %175 = arith.muli %173, %c3_i64_18 : i64
    %176 = arith.addi %175, %174 : i64
    %177 = arith.index_cast %176 : i64 to index
    %178 = memref.load %arg2[%177] {handshake.name = "load19"} : memref<9xf32>
    %179 = arith.extf %178 : f32 to f64
    %180 = arith.divf %172, %179 : f64
    %181 = arith.truncf %180 : f64 to f32
    %182 = arith.extui %142 : i32 to i64
    %183 = arith.extui %104 : i32 to i64
    %c3_i64_19 = arith.constant 3 : i64
    %184 = arith.muli %182, %c3_i64_19 : i64
    %185 = arith.addi %184, %183 : i64
    %186 = arith.index_cast %185 : i64 to index
    memref.store %181, %arg1[%186] {handshake.deps = #handshake<deps[{dstAccess : "store11", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load12", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load16", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store20"} : memref<9xf32>
    cf.br ^bb25
  ^bb25:  // 2 preds: ^bb21, ^bb24
    %187 = arith.addi %142, %c1_i32 : i32
    %188 = arith.cmpi ult, %187, %c3_i32 : i32
    cf.cond_br %188, ^bb17(%187 : i32), ^bb26
  ^bb26:  // pred: ^bb25
    %189 = arith.addi %104, %c1_i32 : i32
    %190 = arith.cmpi ult, %189, %c3_i32 : i32
    cf.cond_br %190, ^bb16(%189 : i32), ^bb27
  ^bb27:  // pred: ^bb26
    return
  }
}
