#include "231DFA.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/GlobalVariable.h"
#include <map>
#include <set>

using namespace llvm;
typedef std::pair<char,unsigned> PtrID;

namespace{
    //define a subclass of Info: MayPointToInfo
    class MayPointToInfo: public Info  
    {
        public:
            std::map<PtrID,std::set<PtrID>> MayPointMap;

            MayPointToInfo(){}
            MayPointToInfo(const MayPointToInfo &other):Info(other){
                MayPointMap=other.MayPointMap;
            }
            //Implement virtual function of parent class to print reaching definition
            void print(){
                for(auto iter:MayPointMap){
                    errs()<<iter.first.first<<iter.first.second<<"->(";
                    for(auto iter2:iter.second){
                        errs()<<iter2.first<<iter2.second<<'/';
                    }
                    errs()<<")|";
                }
                errs()<<"\n";
            }
            //Implement equal function 
            static bool equals(MayPointToInfo* info1, MayPointToInfo* info2){
                return info1->MayPointMap==info2->MayPointMap;
            }
            //Implement join() function
            static MayPointToInfo* join(MayPointToInfo* info1, MayPointToInfo* info2, MayPointToInfo* result){
                result->MayPointMap=info1->MayPointMap;
                for(auto KeyVal:info2->MayPointMap){
                    if(result->MayPointMap.find(KeyVal.first)==result->MayPointMap.end()){
                        (result->MayPointMap)[KeyVal.first]=KeyVal.second;
                    }else{
                        std::set_union((result->MayPointMap)[KeyVal.first].begin(),(result->MayPointMap)[KeyVal.first].end(),(info2->MayPointMap)[KeyVal.first].begin(),(info2->MayPointMap)[KeyVal.first].end(),std::inserter((result->MayPointMap)[KeyVal.first],(result->MayPointMap)[KeyVal.first].end()));
                    }
                }
                return result;
            }
    };
    //define a subclass of DataFlowAnalysis: MayPointToDefinitionAnalysis
    class MayPointToDefinitionAnalysis: public DataFlowAnalysis<MayPointToInfo,true> {
        private:
            //Implement flowfunction to process three types of instructions
            void flowfunction(Instruction * I,std::vector<unsigned> & IncomingEdges,std::vector<unsigned> & OutgoingEdges,std::vector<MayPointToInfo *> & InfoOut){
                unsigned curNodeIndex=InstrToIndex[I];
                std::string instrName=I->getOpcodeName();

                //Join all infos on all incomingEdges
                MayPointToInfo AllInfoIn;
                for(auto edgeIndex: IncomingEdges){
                    MayPointToInfo* tmpInfo=EdgeToInfo[std::make_pair(edgeIndex,curNodeIndex)];
                    MayPointToInfo::join(&AllInfoIn,tmpInfo,&AllInfoIn);
                }

                if(instrName=="alloca"){
                    AllInfoIn.MayPointMap[PtrID('R',curNodeIndex)].insert(PtrID('M',curNodeIndex));
                }else if(instrName=="bitcast"||instrName=="getelementptr"){
                    Instruction* srcInstr;
                    if(instrName=="bitcast")
                        srcInstr=dyn_cast<Instruction>(I->getOperand(0));
                    else
                        srcInstr=dyn_cast<Instruction>((dyn_cast<GetElementPtrInst>(I))->getPointerOperand());
                    if(AllInfoIn.MayPointMap.find(PtrID('R',InstrToIndex[srcInstr]))!=AllInfoIn.MayPointMap.end()){
                        for(auto iter:AllInfoIn.MayPointMap[PtrID('R',InstrToIndex[srcInstr])]){
                            AllInfoIn.MayPointMap[PtrID('R',curNodeIndex)].insert(iter);
                        }
                    }
                }else if(instrName=="load"){
                    Instruction* srcInstr=dyn_cast<Instruction>((dyn_cast<LoadInst>(I))->getPointerOperand());
                    if(AllInfoIn.MayPointMap.find(PtrID('R',InstrToIndex[srcInstr]))!=AllInfoIn.MayPointMap.end()){
                        for(auto iter:AllInfoIn.MayPointMap[PtrID('R',InstrToIndex[srcInstr])]){
                            if(AllInfoIn.MayPointMap.find(iter)!=AllInfoIn.MayPointMap.end()){
                                for(auto iter2:AllInfoIn.MayPointMap[iter]){
                                    AllInfoIn.MayPointMap[PtrID('R',curNodeIndex)].insert(iter2);
                                }
                            }
                        }
                    }
                }else if(instrName=="store"){
                    std::set<PtrID> srcSet;
                    std::set<PtrID> dstSet;
                    Instruction* srcInstr=dyn_cast<Instruction>((dyn_cast<StoreInst>(I))->getValueOperand());
                    if(AllInfoIn.MayPointMap.find(PtrID('R',InstrToIndex[srcInstr]))!=AllInfoIn.MayPointMap.end()){
                        srcSet=AllInfoIn.MayPointMap[PtrID('R',InstrToIndex[srcInstr])];
                    }
                    Instruction* dstInstr=dyn_cast<Instruction>((dyn_cast<StoreInst>(I))->getPointerOperand());
                    if(AllInfoIn.MayPointMap.find(PtrID('R',InstrToIndex[dstInstr]))!=AllInfoIn.MayPointMap.end()){
                        dstSet=AllInfoIn.MayPointMap[PtrID('R',InstrToIndex[dstInstr])];
                    }
                    for(auto iter1:dstSet){
                        for(auto iter2:srcSet){
                            AllInfoIn.MayPointMap[iter1].insert(iter2);     //No matter AllInfoIn.MayPointMap[iter1] exists or not, this will work. If it doesn't exist, it will create a pair and insert iter2 to an empty set. If it exists, it will just insert to existing set.
                        }
                    }
                }else if(instrName=="select"){
                    Instruction* srcInstr1=dyn_cast<Instruction>((dyn_cast<SelectInst>(I))->getTrueValue());
                    if(AllInfoIn.MayPointMap.find(PtrID('R',InstrToIndex[srcInstr1]))!=AllInfoIn.MayPointMap.end()){
                        for(auto iter:AllInfoIn.MayPointMap[PtrID('R',InstrToIndex[srcInstr1])]){
                            AllInfoIn.MayPointMap[PtrID('R',curNodeIndex)].insert(iter);
                        }
                    }
                    Instruction* srcInstr2=dyn_cast<Instruction>((dyn_cast<SelectInst>(I))->getFalseValue());
                    if(AllInfoIn.MayPointMap.find(PtrID('R',InstrToIndex[srcInstr2]))!=AllInfoIn.MayPointMap.end()){
                        for(auto iter:AllInfoIn.MayPointMap[PtrID('R',InstrToIndex[srcInstr2])]){
                            AllInfoIn.MayPointMap[PtrID('R',curNodeIndex)].insert(iter);
                        }
                    }
                }else if(instrName=="phi"){
                    BasicBlock * parentBlock=I->getParent();    //get the block that the first phi instruction belongs to
                    unsigned nonPhiIndex=InstrToIndex[parentBlock->getFirstNonPHI()];       //get the index of the first Non-phi instruction

                    for(unsigned j=curNodeIndex;j<nonPhiIndex;++j){     //Iterate through phi nodes
                        PHINode* curPhiNode=dyn_cast<PHINode>(IndexToInstr[j]);
                        unsigned PhiOperandNum=curPhiNode->getNumIncomingValues();  //Get how many operands (<value,block> pairs) this phi node has
                        for(unsigned k=0;k<PhiOperandNum;++k){      //Iterate through all pairs
                            Value* operandValue=curPhiNode->getIncomingValue(k);
                            Instruction* OperandInstr=dyn_cast<Instruction>(operandValue);  //Get the instruction where the value in the pair is defined
                            if(AllInfoIn.MayPointMap.find(PtrID('R',InstrToIndex[OperandInstr]))!=AllInfoIn.MayPointMap.end()){
                                for(auto iter:AllInfoIn.MayPointMap[PtrID('R',InstrToIndex[OperandInstr])]){
                                    AllInfoIn.MayPointMap[PtrID('R',curNodeIndex)].insert(iter);
                                }
                            }
                        }
                    }
                }
                for(unsigned i=0;i<InfoOut.size();++i)
                    InfoOut[i]->MayPointMap=AllInfoIn.MayPointMap;
    
            }
        public:
            //the constructor which explicitly call the constructor of parent class
            MayPointToDefinitionAnalysis(MayPointToInfo& bottom, MayPointToInfo& initialState):DataFlowAnalysis(bottom,initialState){}
    };

    struct MayPointToDefinitionAnalysisPass:public FunctionPass {
        static char ID;
        MayPointToDefinitionAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            //define bottom and initialState in lattice
            MayPointToInfo bottom=MayPointToInfo();
            MayPointToInfo initialState=MayPointToInfo();
            MayPointToDefinitionAnalysis ReachDefAnalysis=MayPointToDefinitionAnalysis(bottom,initialState);

            ReachDefAnalysis.runWorklistAlgorithm(&F);  //Use the worklist algorithm to analyze the reaching definition 
            ReachDefAnalysis.print();   //Print result

            return false;
        }
    };
}

char MayPointToDefinitionAnalysisPass::ID = 0;
static RegisterPass<MayPointToDefinitionAnalysisPass> X("cse231-maypointto", "Developed to analyze may point to information of pointers", false /* Only looks at CFG */, false /* Analysis Pass */);