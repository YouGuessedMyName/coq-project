src/Mealy.vo src/Mealy.glob src/Mealy.v.beautified src/Mealy.required_vo: src/Mealy.v 
src/Mealy.vio: src/Mealy.v 
src/Mealy.vos src/Mealy.vok src/Mealy.required_vos: src/Mealy.v 
src/FunctionalSimulation.vo src/FunctionalSimulation.glob src/FunctionalSimulation.v.beautified src/FunctionalSimulation.required_vo: src/FunctionalSimulation.v src/Mealy.vo
src/FunctionalSimulation.vio: src/FunctionalSimulation.v src/Mealy.vio
src/FunctionalSimulation.vos src/FunctionalSimulation.vok src/FunctionalSimulation.required_vos: src/FunctionalSimulation.v src/Mealy.vos
