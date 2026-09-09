## Round-trip, tag isolation and CRC failure tests for stage checkpoints.
import std/[os,tempfiles]
import modular_matrix, ideal_checkpoint
let directory=createTempDir("hecke-checkpoint-","")
let path=directory / "stage.gz"
let A=init_mod_matrix(11,17,2187)
for i in 0..<A.rows:
  for j in 0..<A.columns: A[i,j]=uint64(i*173+j*291) mod 2187
write_checkpoint(path,"producer",86,1,@[A])
let saved=read_checkpoint(path,"producer",86,1)
doAssert saved.len==1 and saved[0]==A
var rejected=false
try: discard read_checkpoint(path,"different-producer",86,1)
except ValueError: rejected=true
doAssert rejected
var content=readFile(path)
content[content.len-8]=char(ord(content[content.len-8]) xor 1)
writeFile(path,content)
rejected=false
try: discard read_checkpoint(path,"producer",86,1)
except IOError: rejected=true
doAssert rejected
removeFile(path)
removeDir(directory)
echo "checkpoint round-trip, producer isolation and CRC tests passed"
