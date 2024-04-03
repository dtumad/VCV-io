git ls-files 'VCVio/*.lean' | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > VCVio.lean
