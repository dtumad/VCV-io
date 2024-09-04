echo "# Building VCVio library"
lake build VCVio

echo "\n# Building examples"
lake build Examples

echo "\n# Linting files"
scripts/lint-style.sh && echo "All files okay"
