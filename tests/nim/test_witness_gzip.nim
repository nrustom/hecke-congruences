## Run against a packet, or with --reject against a deliberately damaged copy.
import std/os
import ../../nim/compact_witnesses

let reject=paramCount()==2 and paramStr(2)=="--reject"
var rejected=false
try:
  discard read_witness_data(paramStr(1))
except IOError, ValueError:
  rejected=true
doAssert rejected==reject
echo "gzip packet check passed"
