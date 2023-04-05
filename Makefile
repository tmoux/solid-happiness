all: agda graph

agda:
	agda --safe Everything.agda --dependency-graph=dep.dot

graph:
	filter-agda-dependency-graph < dep.dot > small.dot
	dot -Tpdf small.dot > small.pdf
