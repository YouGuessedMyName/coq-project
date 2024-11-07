src/Mealy.vo src/Mealy.glob src/Mealy.v.beautified src/Mealy.required_vo: src/Mealy.v 
src/Mealy.vio: src/Mealy.v 
src/Mealy.vos src/Mealy.vok src/Mealy.required_vos: src/Mealy.v 
src/FunctionalSimulation.vo src/FunctionalSimulation.glob src/FunctionalSimulation.v.beautified src/FunctionalSimulation.required_vo: src/FunctionalSimulation.v src/Mealy.vo
src/FunctionalSimulation.vio: src/FunctionalSimulation.v src/Mealy.vio
src/FunctionalSimulation.vos src/FunctionalSimulation.vok src/FunctionalSimulation.required_vos: src/FunctionalSimulation.v src/Mealy.vos
src/ObservationTree.vo src/ObservationTree.glob src/ObservationTree.v.beautified src/ObservationTree.required_vo: src/ObservationTree.v src/Mealy.vo src/FunctionalSimulation.vo
src/ObservationTree.vio: src/ObservationTree.v src/Mealy.vio src/FunctionalSimulation.vio
src/ObservationTree.vos src/ObservationTree.vok src/ObservationTree.required_vos: src/ObservationTree.v src/Mealy.vos src/FunctionalSimulation.vos
src/Bisimulation.vo src/Bisimulation.glob src/Bisimulation.v.beautified src/Bisimulation.required_vo: src/Bisimulation.v src/Mealy.vo
src/Bisimulation.vio: src/Bisimulation.v src/Mealy.vio
src/Bisimulation.vos src/Bisimulation.vok src/Bisimulation.required_vos: src/Bisimulation.v src/Mealy.vos
