
let impscript_dir = "../" (* TODO use environment variable *)
let out_dir = impscript_dir ^ "src/out/"
let prims_file = impscript_dir ^ "prims/prims.is"
let out_filename = impscript_dir ^ "src/out/output_filename"
let ace_dir = impscript_dir ^ "ace-output/"

let castInsertionMode = ref true
let strictObjGet = ref false
