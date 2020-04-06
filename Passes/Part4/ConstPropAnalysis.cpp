#include "231DFA.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/Analysis/CallGraph.h"
#include <set>
#include <map>
#include <iostream>

using namespace llvm;

namespace{

    std::set<Value*> MPT;
    std::set<GlobalVariable*> GlobMPT;
    std::map<Function*, std::set<GlobalVariable*>> MOD;

    bool isPointerToPointer(Value* v){
        Type* t=v->getType();
        return t->isPointerTy() && t->getContainedType(0)->isPointerTy();
    }

    class ConstPropInfo:public Info{
        public:
            enum ConstState { Bottom, Const, Top };
            struct ConstVal { 
                ConstState state ; 
                Constant* value;
                ConstVal(){}
                ConstVal(ConstState State,Constant* Value):state(State),value(Value){}
                friend bool operator == (const ConstVal& left, const ConstVal& right){
                    if(left.state==right.state){
                        if(left.state==Top||left.state==Bottom)
                            return true;
                        else
                            return left.value==right.value;
                    }else{
                        return false;
                    }
                }; 
            };

            std::map<Value*, struct ConstVal> ConstPropContent;

            ConstPropInfo(){}
            ConstPropInfo(ConstVal val, std::set<GlobalVariable*> globVars){
                for(auto& glob: globVars){
                    ConstPropContent[glob]=val;
                }
            }
            ConstPropInfo(const ConstPropInfo &other):Info(other){
                ConstPropContent=other.ConstPropContent;
            }
            //Implement virtual function of parent class to print reaching definition
            void print(){
                for(auto& iter:ConstPropContent){
                    if(false==isa<GlobalVariable>(iter.first))
                        continue;
                    errs()<<iter.first->getName()<<"=";
                    if(Bottom==iter.second.state){
                        errs()<<"⊥";
                    }else if(Top==iter.second.state){
                        errs()<<"⊤";
                    }else{
                        errs()<<*iter.second.value;
                    }
                    errs()<<"|";
                }
                errs()<<"\n";
            }
            // Implement equal function 
            static bool equals(ConstPropInfo* info1, ConstPropInfo* info2){
                return info1->ConstPropContent==info2->ConstPropContent;
            }
            //Implement join() function
            static ConstPropInfo* join(ConstPropInfo* info1, ConstPropInfo* info2, ConstPropInfo* result){
                for(auto& pair: info1->ConstPropContent){
                    auto val1=pair.second;
                    if(info2->ConstPropContent.find(pair.first)!=info2->ConstPropContent.end()){ //info2 also has this variable
                        auto val2=info2->ConstPropContent[pair.first];
                        if(val1.state==Top){
                            result->ConstPropContent[pair.first]=ConstVal(Top,nullptr);   //still top
                        }else if(val1.state==Const){
                            if(val2.state==Top)
                                result->ConstPropContent[pair.first]=ConstVal(Top,nullptr);   //still top
                            else if(val2.state==Bottom)
                                result->ConstPropContent[pair.first]=val1;           // result is the same with info1
                            else{
                                result->ConstPropContent[pair.first]=(val2==val1)?val1:ConstVal(Top,nullptr);  // if both const are the same, result is the same const, else top
                            }
                        }else{
                            result->ConstPropContent[pair.first]=val2;   // if info1 is bottom, then the result will be whatever info2 is
                        }
                    }else{
                        // result->ConstPropContent[pair.first]=ConstVal(Top,nullptr);
                        result->ConstPropContent[pair.first]=val1;   
                    }
                }
                return result;
            }
    };

    class ConstPropAnalysis: public DataFlowAnalysis<ConstPropInfo,true>{
        private:
            ConstantFolder Folder;
            void flowfunction(Instruction * I,std::vector<unsigned> & IncomingEdges,std::vector<unsigned> & OutgoingEdges,std::vector<ConstPropInfo *> & InfoOut){
                unsigned curNodeIndex=InstrToIndex[I];
                std::string instrName=I->getOpcodeName();

                //Join all infos on all incomingEdges
                ConstPropInfo AllInfoIn=*EdgeToInfo[std::make_pair(IncomingEdges[0],curNodeIndex)];
                for(auto edgeIndex: IncomingEdges){
                    ConstPropInfo* tmpInfo=EdgeToInfo[std::make_pair(edgeIndex,curNodeIndex)];
                    ConstPropInfo::join(&AllInfoIn,tmpInfo,&AllInfoIn);
                }

                //Flowfunction for binary operator
                if(BinaryOperator* binOp=dyn_cast<BinaryOperator>(I)){
                    Value* x=I->getOperand(0);
                    Value* y=I->getOperand(1);
                    Constant* x_const=dyn_cast<Constant>(x);
                    Constant* y_const=dyn_cast<Constant>(y);
                    if(!x_const){
                        if(AllInfoIn.ConstPropContent.find(x)!=AllInfoIn.ConstPropContent.end()
                            && AllInfoIn.ConstPropContent[x].state==ConstPropInfo::Const)
                            x_const=AllInfoIn.ConstPropContent[x].value;
                    }
                    if(!y_const){
                        if(AllInfoIn.ConstPropContent.find(y)!=AllInfoIn.ConstPropContent.end()
                            && AllInfoIn.ConstPropContent[y].state==ConstPropInfo::Const)
                            y_const=AllInfoIn.ConstPropContent[y].value;
                    }
                    if(x_const && y_const){
                        AllInfoIn.ConstPropContent[I]=ConstPropInfo::ConstVal(ConstPropInfo::Const,Folder.CreateBinOp(binOp->getOpcode(),x_const,y_const));
                    }else{
                        AllInfoIn.ConstPropContent[I]=ConstPropInfo::ConstVal(ConstPropInfo::Top,nullptr);
                    }
                }
                //Flowfunction for unary operator
                else if(UnaryOperator* unaOp=dyn_cast<UnaryOperator>(I)){
                    Value* x=I->getOperand(0);
                    Constant* x_const=dyn_cast<Constant>(x);
                    if(!x_const){
                        if(AllInfoIn.ConstPropContent.find(x)!=AllInfoIn.ConstPropContent.end()
                            && AllInfoIn.ConstPropContent[x].state==ConstPropInfo::Const)
                            x_const=AllInfoIn.ConstPropContent[x].value;
                    }
                    if(x_const){
                        AllInfoIn.ConstPropContent[I]=ConstPropInfo::ConstVal(ConstPropInfo::Const,Folder.CreateUnOp(unaOp->getOpcode(),x_const));
                    }else{
                        AllInfoIn.ConstPropContent[I]=ConstPropInfo::ConstVal(ConstPropInfo::Top,nullptr);
                    }
                }
                //Flowfunction for compare operator
                else if(CmpInst* cmpOp=dyn_cast<CmpInst>(I)){
                    Value* x=I->getOperand(0);
                    Value* y=I->getOperand(1);
                    Constant* x_const=dyn_cast<Constant>(x);
                    Constant* y_const=dyn_cast<Constant>(y);
                    if(!x_const){
                        if(AllInfoIn.ConstPropContent.find(x)!=AllInfoIn.ConstPropContent.end()
                            && AllInfoIn.ConstPropContent[x].state==ConstPropInfo::Const)
                            x_const=AllInfoIn.ConstPropContent[x].value;
                    }
                    if(!y_const){
                        if(AllInfoIn.ConstPropContent.find(y)!=AllInfoIn.ConstPropContent.end()
                            && AllInfoIn.ConstPropContent[y].state==ConstPropInfo::Const)
                            y_const=AllInfoIn.ConstPropContent[y].value;
                    }
                    if(x_const && y_const){
                        if(instrName=="icmp")
                            AllInfoIn.ConstPropContent[I]=ConstPropInfo::ConstVal(ConstPropInfo::Const,Folder.CreateICmp(cmpOp->getPredicate(),x_const,y_const));
                        else
                            AllInfoIn.ConstPropContent[I]=ConstPropInfo::ConstVal(ConstPropInfo::Const,Folder.CreateFCmp(cmpOp->getPredicate(),x_const,y_const));
                    }else{
                        AllInfoIn.ConstPropContent[I]=ConstPropInfo::ConstVal(ConstPropInfo::Top,nullptr);
                    }
                }
                //Flowfunction for select operator
                else if(SelectInst* selOp=dyn_cast<SelectInst>(I)){
                    Value* x=I->getOperand(0);
                    Value* y=I->getOperand(1);
                    Constant* x_const=dyn_cast<Constant>(x);
                    Constant* y_const=dyn_cast<Constant>(y);
                    if(!x_const){
                        if(AllInfoIn.ConstPropContent.find(x)!=AllInfoIn.ConstPropContent.end()
                            && AllInfoIn.ConstPropContent[x].state==ConstPropInfo::Const)
                            x_const=AllInfoIn.ConstPropContent[x].value;
                    }
                    if(!y_const){
                        if(AllInfoIn.ConstPropContent.find(y)!=AllInfoIn.ConstPropContent.end()
                            && AllInfoIn.ConstPropContent[y].state==ConstPropInfo::Const)
                            y_const=AllInfoIn.ConstPropContent[y].value;
                    }
                    if(x_const && y_const){
                        if(Constant* condition=dyn_cast<Constant>(selOp->getCondition()))
                            AllInfoIn.ConstPropContent[I]=ConstPropInfo::ConstVal(ConstPropInfo::Const,Folder.CreateSelect(condition,x_const,y_const));
                    }else{
                        AllInfoIn.ConstPropContent[I]=ConstPropInfo::ConstVal(ConstPropInfo::Top,nullptr);
                    }
                }
                //Flowfunction for call instruction
                else if(CallInst* callOp=dyn_cast<CallInst>(I)){
                    for(auto& glob: MOD[callOp->getCalledFunction()]){
                        AllInfoIn.ConstPropContent[glob]=ConstPropInfo::ConstVal(ConstPropInfo::Top,nullptr);
                    }
                }
                //Flowfunction for load instruction
                else if(LoadInst* loadOp=dyn_cast<LoadInst>(I)){
                    if(!I->getType()->isPointerTy()){
                        AllInfoIn.ConstPropContent[I]=AllInfoIn.ConstPropContent[loadOp->getPointerOperand()];
                    }else{
                        AllInfoIn.ConstPropContent[I]=ConstPropInfo::ConstVal(ConstPropInfo::Top,nullptr);
                    }
                }
                //Flowfunction for store instruction
                else if(StoreInst* storeOp=dyn_cast<StoreInst>(I)){
                    Value* src=storeOp->getValueOperand();
                    Value* dst=storeOp->getPointerOperand();
                    if(Constant* srcVal=dyn_cast<Constant>(src)){
                        AllInfoIn.ConstPropContent[dst]=ConstPropInfo::ConstVal(ConstPropInfo::Const,srcVal);
                    }else{
                        if(!src->getType()->isPointerTy()){
                            AllInfoIn.ConstPropContent[dst]=AllInfoIn.ConstPropContent[src];
                        }
                    }
                }
                //Flowfunction for Phi instruction
                else if(PHINode* phiOp=dyn_cast<PHINode>(I)){
                    unsigned nonPhiIndex=InstrToIndex[I->getParent()->getFirstNonPHI()];
                    for(unsigned i=curNodeIndex;i<nonPhiIndex;i++){
                        PHINode* phiNode=dyn_cast<PHINode>(IndexToInstr[i]);
                        unsigned phiOperandNum=phiNode->getNumIncomingValues();
                        ConstPropInfo::ConstVal prevConstVal;
                        if(isa<Constant>(phiNode->getIncomingValue(0))){
                            prevConstVal.state=ConstPropInfo::Const;
                            prevConstVal.value=dyn_cast<Constant>(phiNode->getIncomingValue(0));
                        }else{
                            prevConstVal.state=ConstPropInfo::Top;
                            prevConstVal.value=nullptr;
                        }
                        bool sameFlag=true;
                        for(unsigned j=1;j<phiOperandNum;j++){
                            if(Value* val=dyn_cast<Constant>(phiNode->getIncomingValue(j))){
                                if(val!=prevConstVal.value){
                                    sameFlag=false;
                                    break;
                                }
                            }else{
                                sameFlag=false;
                                break;
                            }
                        }
                        if(sameFlag){
                            AllInfoIn.ConstPropContent[IndexToInstr[i]]=prevConstVal;
                        }else{
                            AllInfoIn.ConstPropContent[IndexToInstr[i]]=ConstPropInfo::ConstVal(ConstPropInfo::Top,nullptr);
                        }
                    }
                }
                
                for(unsigned i=0;i<InfoOut.size();++i){
                    InfoOut[i]->ConstPropContent=AllInfoIn.ConstPropContent;
                }
            }
        public:
            //the constructor which explicitly call the constructor of parent class
            ConstPropAnalysis(ConstPropInfo& bottom, ConstPropInfo& initialState):DataFlowAnalysis(bottom,initialState){}

    };



    struct ConstPropAnalysisPass:public CallGraphSCCPass {
        static char ID;
        ConstPropAnalysisPass() : CallGraphSCCPass(ID) {}

        bool doInitialization(CallGraph &CG) override{
            auto& globalVariableList=CG.getModule().getGlobalList();

            //********************MPT Analysis***********************
            //global variable initialization reference
            for(auto& variable: globalVariableList){
                if(isa<GlobalVariable>(variable.getInitializer()))
                    MPT.insert(dyn_cast<GlobalVariable>(variable.getInitializer()));    // dyn_cast may fail, so may need to use try catch?
            }
            //local variable, function parameter and return value
            for(auto& func: CG.getModule().functions()){
                for(auto& block: func){
                    for(auto& instr: block){
                        if(isa<StoreInst>(instr)){     // local variable initialization reference
                            Value* srcVal=(dyn_cast<StoreInst>(&instr))->getValueOperand();
                            if(false==isa<Constant>(srcVal))
                                MPT.insert(srcVal);
                        }else if(isa<CallInst>(instr)){
                            for(Use& operand: instr.operands()){
                                MPT.insert(operand);            // reference parameters in function call
                            }
                        }else if(isa<ReturnInst>(instr)){
                            for(Use& operand: instr.operands()){
                                MPT.insert(operand);            // return value reference
                            }
                        }
                    }
                }
            }
            //get global variables in MPT set and form GlobMPT set
            for(auto& var: MPT){
                if(isa<GlobalVariable>(var)){
                    GlobMPT.insert(dyn_cast<GlobalVariable>(var));
                }
            }

            //********************LMOD Analysis***********************
            for(auto& func: CG.getModule().functions()){
                for(auto& block: func){
                    for(auto& instr: block){
                        if(isa<StoreInst>(instr)){
                            Value* dstVal=(dyn_cast<StoreInst>(&instr))->getPointerOperand();
                            if(isa<GlobalVariable>(dstVal))
                                MOD[&func].insert(dyn_cast<GlobalVariable>(dstVal));    //global variable is directly modified
                            else if(isPointerToPointer(dstVal)){
                                MOD[&func].insert(GlobMPT.begin(),GlobMPT.end());       //dereference pointer is modified
                            }
                        }
                    }
                }
            }

            return false;
        }

        bool runOnSCC(CallGraphSCC &SCC) override{
            //********************CMOD Analysis***********************
            std::set<GlobalVariable*> tmpSet;
        
            for(auto& callerNode: SCC){
                Function* caller=callerNode->getFunction();
                for(auto& record: *callerNode){      // get callee info outside current SCC (callee info inside current SCC is also involved, but doesn't matter)
                    Function* callee=record.second->getFunction();
                    if(MOD.find(callee)!=MOD.end())
                        MOD[caller].insert(MOD[callee].begin(),MOD[callee].end());
                }
                //union info of each caller function to solve the loop issue
                tmpSet.insert(MOD[caller].begin(),MOD[caller].end());
            }

            for(auto& callerNode: SCC){
                Function* caller=callerNode->getFunction();
                MOD[caller]=tmpSet;
            }

            return false;
        }

        bool doFinalization(CallGraph &CG) override{
            std::set<GlobalVariable*> globSet;
            for(auto& glob: CG.getModule().getGlobalList()){
                globSet.insert(&glob);
            }

            for(Function& F: CG.getModule().functions()){
                ConstPropInfo bottom=ConstPropInfo(ConstPropInfo::ConstVal(ConstPropInfo::Bottom,nullptr),globSet);
                ConstPropInfo initialState=ConstPropInfo(ConstPropInfo::ConstVal(ConstPropInfo::Top,nullptr),globSet);
                ConstPropAnalysis analysis=ConstPropAnalysis(bottom,initialState);
                analysis.runWorklistAlgorithm(&F);
                analysis.print();
            }
            return false;
        }
    };

}

char ConstPropAnalysisPass::ID = 0;
static RegisterPass<ConstPropAnalysisPass> X("cse231-constprop", "Developed to realize constant propagation", false /* Only looks at CFG */, false /* Analysis Pass */);