#include <set>
#include <iterator>
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"
#include "string"
#include "iostream"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "set"
#include "iterator"

using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::driver;
using namespace clang::tooling;

static llvm::cl::OptionCategory MatcherSampleCategory("Matcher Sample");
SourceLocation funcloc;
const LabelStmt *LS;
const FunctionDecl *FS;
std::string str, str1;
int ast = 1;

std::string bindvar="forLabel";
int labelnum = 0;
typedef std::pair <std::string,std::string> varPair;
std::set<varPair> varSet;
std::set<std::string> vardeclSet;
std::set<clang::SourceLocation> DREset;
int labelcount =0;


bool hasEnding (std::string const &fullString, std::string const &ending) {
    if (fullString.length() >= ending.length()) {
        return (0 == fullString.compare (fullString.length() - ending.length(), ending.length(), ending));
    } else {
        return false;
    }
}



class RecordHandler: public MatchFinder::MatchCallback{

	public:
		RecordHandler(Rewriter &Rewrite): Rewrite(Rewrite) {}

		virtual void run(const MatchFinder::MatchResult &Result){
			
			const RecordDecl *RD = Result.Nodes.getNodeAs<clang::RecordDecl>("structure");

		//	std::cout<<RD->getNameAsString();
			clang::SourceManager *sm1 = Result.SourceManager;
			clang::LangOptions lopt1;

			SourceRange srs(RD->getBeginLoc(), RD->getEndLoc());
			std::string rr = Rewrite.getRewrittenText(srs);
			
			clang::SourceLocation b(RD->getBeginLoc()), _e(RD->getEndLoc());
                        clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, *sm1, lopt1));

		//	str1 = std::string(sm1->getCharacterData(b),sm1->getCharacterData(e)-sm1->getCharacterData(b));
                                Rewrite.InsertText(funcloc,rr+";\n\n", true, true);

                               //  Rewrite.InsertText(RD->getBeginLoc(),"/*",true,true);
                               // Rewrite.InsertTextAfterToken(RD->getEndLoc(),"*/");
			      // clang::Rewriter::RewriteOptions opts=RewriteOptions();
			    //  Rewrite.RemoveText(srs,opts);
			     		  Rewrite.ReplaceText(srs,"");
					Rewrite.ReplaceText(e,"");
		}
		private:

			Rewriter &Rewrite;
		};

//-------------------------------------------------------------------------------------------------------------------------------------------

class DeclVarHandler: public MatchFinder::MatchCallback{

	public:
		DeclVarHandler(Rewriter &Rewrite): Rewrite(Rewrite) {}

                virtual void run(const MatchFinder::MatchResult &Result){

                const VarDecl *VD = Result.Nodes.getNodeAs<clang::VarDecl>("declvar");
		
		const LabelStmt *LS3 = Result.Nodes.getNodeAs<clang::LabelStmt>(bindvar+std::to_string(labelnum));

	//	if (LS == LS3)
		{

				if(VD)
				{
					std::string varName2 = VD->getNameAsString();
					vardeclSet.insert(varName2);
				//	QualType QT2 = VD->getType();
		        //  std::string varType2 = QT2.getAsString();
				//	std::cout<<"\n"<<" label "<<LS->getName()<<"   var T N == "<<varType2<<" || "<<varName2 ;
				}
				}
	}
		private:
        	Rewriter &Rewrite;

};

//--------------------------------------------------------------------------------------------------------------------------------------------


class VariableHandler: public MatchFinder::MatchCallback{

	public:
		VariableHandler(Rewriter &Rewrite): Rewrite(Rewrite) {}

                virtual void run(const MatchFinder::MatchResult &Result){

                const DeclRefExpr *DS = Result.Nodes.getNodeAs<clang::DeclRefExpr>("forVar");
				DeclarationNameInfo varInfo = DS->getNameInfo();
                DeclarationName varDec = varInfo.getName();
                std::string varName = varDec.getAsString();

              	
		//		const LabelStmt *LS2 = Result.Nodes.getNodeAs<clang::LabelStmt>(bindvar+std::to_string(labelnum));
			   	const LabelStmt *LS2 = Result.Nodes.getNodeAs<clang::LabelStmt>("declabel");

				const FunctionDecl *FS2 = Result.Nodes.getNodeAs<clang::FunctionDecl>("isit");


		         clang::SourceManager *smVH = Result.SourceManager;
			      BeforeThanCompare<clang::SourceLocation> isBefore(*smVH);


		if (FS == FS2  && isBefore(DS->getBeginLoc(),LS->getEndLoc()) && isBefore(LS->getBeginLoc(),DS->getBeginLoc())) 
				
		{

					DeclarationNameInfo DNI1 = FS2->getNameInfo();
               		DeclarationName DN1 = DNI1.getName();
                	std::string fname = DN1.getAsString();


			 if (const clang::VarDecl* VD = dyn_cast<clang::VarDecl>(DS->getDecl()))
				
			 {
					DeclarationNameInfo varInfo = DS->getNameInfo();
					DeclarationName varDec = varInfo.getName();
					std::string varName = varDec.getAsString();

						
					if((vardeclSet.find(varName))==(vardeclSet.end())) // wo variable abhi tak define to ni hai
					
					{
						int prev = DREset.size();
						DREset.insert(DS->getBeginLoc());

						//std::cout<<"var+label  "<<varName<<"  "<<LS->getName()<<"\n";
					if(DREset.size()>prev)
						{
							
											unsigned int varnameLen = varName.size();
		                                	const ValueDecl *VT = DS->getDecl();
		                                	QualType QT = VT->getType();
		                                	std::string varType = QT.getAsString();
		                                	//const Type *type = QT.getTypePtr();

							if(varType.rfind("struct",0)==0)
							{
			
							    Rewrite.ReplaceText(DS->getBeginLoc(),varnameLen,"(*"+varName+"_"+LS->getName()+")");
							}



                        	//else if(type->isConstantArrayType())
                        	//{
                            	

                        		else if (varType.find("[") != std::string::npos)
								 {

								 	
		                                	ASTContext *Context1 = Result.Context;
		                                	const ConstantArrayType *cat = Context1->getAsConstantArrayType(QT);
		                                	const llvm::APInt apint = cat->getSize();
		                                	int dim = apint.getLimitedValue(1000000);

								 	int count = 0;
								 	std::string repeat = "_0_";
								 	//int dim = type->getSize();




						 			for(int z = 0; z < varType.size();z++)
						 			{
						 				if(varType[z] == '[')
						 				count++;
						 			}

						 			for(int z = 0;z<count;z++)
						 			{
						 				repeat+="_";
						 			}

                            	//const ArrayType *Array = type->castAsArrayTypeUnsafe();
                            	//cout << "Is array of type: "  << Array->getElementType().getAsString() << endl;
						 			varName+=std::to_string(dim);
                            	Rewrite.ReplaceText(DS->getBeginLoc(),varnameLen,varName+ repeat);
                            	
                        	}

                        	else if(hasEnding(varName,"__"))	
                        	{
                        		Rewrite.ReplaceText(DS->getBeginLoc(),varnameLen,varName);
                        	}
							
							else
							{	
							//	std::cout<<" variable is :  "<<varName<<"||  lebel is: "<<LS->getName()<<" ||function is"<<fname<<"\n";
							Rewrite.ReplaceText(DS->getBeginLoc(),varnameLen,"*"+varName+"_"+LS->getName());
							
							}	

		                         varPair VP = make_pair(varName,varType);
		                        // std::cout<<"\n"<<" vars "<<varType<<" "<<varName;
		                          varSet.insert(VP);

						}
				        }	
				}
			}
	}
		private:
		Rewriter &Rewrite;

};



//--------------------------------------------------------------------------------------------------------------------------------------------



class FunctionHandler: public MatchFinder::MatchCallback{

	public :
		FunctionHandler(Rewriter &Rewrite): Rewrite(Rewrite) {}

		virtual void run(const MatchFinder::MatchResult &Result){

		FS = Result.Nodes.getNodeAs<clang::FunctionDecl>("forFunc");
		if (FS)
		{

			funcloc = FS->getBeginLoc();
			if(FS->getNumParams() > 0)
			{
				ArrayRef<ParmVarDecl * > pvr = FS->parameters();
				std::string arg0 = pvr[0]->getQualifiedNameAsString();
			}


		}
		}

		private:
		Rewriter &Rewrite;

};



//---------------------------------------------------------------------------------------------------------------------------------------------


class CallExprHandler: public MatchFinder::MatchCallback{

	public :
		CallExprHandler(Rewriter &Rewrite): Rewrite(Rewrite) {}

		virtual void run(const MatchFinder::MatchResult &Result){

		const CallExpr *CE = Result.Nodes.getNodeAs<clang::CallExpr>("forCallExpr");
		const FunctionDecl *FD = CE->getDirectCallee();
		DeclarationNameInfo DNI = FD->getNameInfo();
		DeclarationName DN = DNI.getName();
		std::string funcallname = DN.getAsString();
	     	
		if (CE)
		{

		if((funcallname == LS->getName()))
			{
				labelcount++;
				if(labelcount==1)
				{
					      
					std::set<varPair>::iterator itr2;
					SourceLocation FSRB = CE->getBeginLoc();
					SourceLocation FSRE = CE->getEndLoc();
					unsigned int funnamelen = funcallname.size();
					std::string type="";
					std::string itr2name ="";
					std::string funString="";


					for (itr2 = varSet.begin(); itr2 != varSet.end(); itr2++)
			    			{	
			    				type = (*itr2).second;
			    				itr2name = (*itr2).first;

                            		//std::cout<<"\n"<<" In callExpr  == "<<type<<" "<<(*itr2).first;

			    				if(type.find("[") != std::string::npos || hasEnding(itr2name,"__"))
			    				{
			    					funString+=(*itr2).first+" ,";
			    				}
			    				//else if( )
								else	
								{
									funString+=" &"+(*itr2).first+" ,";
								}
			   			 }

								DeclarationNameInfo DNI2 = FS->getNameInfo();
        		                DeclarationName DN2 = DNI2.getName();
	                	        std::string fname2 = DN2.getAsString();


					funString = funString.substr(0,funString.size()-1);
					Rewrite.ReplaceText(FSRB,funnamelen+1,funcallname+"_"+fname2+"("+funString);
					}		

			}	
		}
		}

		private:
		Rewriter &Rewrite;

};



//--------------------------------------------------------------------------------------------------------------------------------------------


class LabelHandler: public MatchFinder::MatchCallback{

	public: LabelHandler(Rewriter &Rewrite) : Rewrite(Rewrite), HandleForVariable(Rewrite),HandleForDecl(Rewrite)
	,HandlerForCall(Rewrite){}


		virtual void run(const MatchFinder::MatchResult &Result){
			labelcount=0;
	
			std::set<varPair>::iterator itr;
			varSet.clear();
			vardeclSet.clear();
			DREset.clear();
			LS = Result.Nodes.getNodeAs<clang::LabelStmt>("forLabel");

			if (LS)
  	 		{
				labelnum++;
    
//		 Finder1.addMatcher(declRefExpr(hasAncestor(labelStmt(hasAncestor(functionDecl().bind("isit"))).bind(bindvar+std::to_string(labelnum)))).bind("forVar"),&HandleForVariable);

        //         Finder1.addMatcher(declRefExpr(hasAncestor(functionDecl().bind("isit"))).bind("forVar"),&HandleForVariable);




                Finder1.addMatcher(declRefExpr(hasAncestor(labelStmt(hasAncestor(functionDecl().bind("isit"))).bind("declabel"))).bind("forVar"),&HandleForVariable);


				Finder1.addMatcher(varDecl(hasAncestor(labelStmt().bind(bindvar+std::to_string(labelnum)))).bind("declvar"),&HandleForDecl);


					 ASTContext *Context1 = Result.Context;
					 Finder1.matchAST(*Context1);
 				Finder2.addMatcher(callExpr(hasAncestor(functionDecl(hasDescendant(labelStmt().bind(bindvar+std::to_string(labelnum)))))).bind("forCallExpr"),&HandlerForCall);

				Finder2.matchAST(*Context1);
				clang::SourceManager *sm = Result.SourceManager;
				clang::LangOptions lopt;

				const LabelStmt *d = LS;
				std::string varString="";
				std::string name = LS->getName();

				std::string type = "";
				std::string itrname = "";
				for (itr = varSet.begin(); itr != varSet.end(); itr++)
    				{	
						type = (*itr).second;
						itrname = (*itr).first;

						std::cout<<"\n"<<type<<"  "<<itrname;	
						//std::cout<<" \n "<<"label name == "<<name<<" var name and type == "<<type<<" sos "<<(*itr).first;


						 if (type.find("[") != std::string::npos)
						 {
						 	int count = 0;
						 	std::string repeat2 = "";
						 	std::string repeat1 = "_0_";

						 	for(int z = 0; z < type.size();z++)
						 	{
						 		if(type[z] == '[')
						 			count++;
						 	}

							type = type.substr(0,type.find("[")-1);

							for (int z= 0;z<count;z++)
							{
								repeat2+="[]";
								repeat1+="_";
							}
							varString+=type+" "+(*itr).first+repeat1+repeat2+", ";

						 }

						 else if( hasEnding(itrname,"__"))
						 {
						 		int count = 0;
						 		std::string repeat ="";
						 		for(int z = itrname.size()-1; z >= 0;z--)
						 		{
						 			if(itrname[z] == '_')
						 			{
						 			count++;
						 			}
						 			else
						 			{
						 				break;
						 			}
						 		}

						 			for(int z =0;z<count;z++)
						 			{
						 				repeat+="[]";
						 			}
						 		type = type.substr(0,type.find("*")-1);
						 		varString+=type+" "+(*itr).first+repeat+", ";

						 }
						else
						{

						 		varString+=type+" *"+(*itr).first+"_"+name+", ";
						 }

    				}
						varString = varString.substr(0,varString.size()-2);
										
						DeclarationNameInfo DNI2 = FS->getNameInfo();
                        DeclarationName DN2 = DNI2.getName();
                        std::string fname1 = DN2.getAsString();
	



				unsigned int nameLen = name.size();
				Rewrite.ReplaceText(d->getBeginLoc(),nameLen+1,name+"_"+fname1+"("+varString+")");

				Rewrite.InsertText(d->getEndLoc(),"return 0;\n",true,true);

				    clang::SourceLocation b(d->getBeginLoc()), _e(d->getEndLoc());
				    clang::SourceLocation e(clang::Lexer::getLocForEndOfToken(_e, 0, *sm, lopt));

				SourceRange sr(d->getBeginLoc(),d->getEndLoc());
				std::string rsr = Rewrite.getRewrittenText(sr);

    				str = std::string(sm->getCharacterData(b),sm->getCharacterData(e)-sm->getCharacterData(b));
				Rewrite.InsertText(funcloc,rsr+"\n\n", true, true);

    				 Rewrite.InsertText(d->getBeginLoc(),"/*",true,true);
     				Rewrite.InsertTextAfterToken(d->getEndLoc(),"*/");

			}

   		}


		private:
		Rewriter &Rewrite;
		MatchFinder Finder1,Finder2;
		VariableHandler HandleForVariable;
		DeclVarHandler HandleForDecl;
		CallExprHandler HandlerForCall;
	};


//-------------------------------------------------------------------------------------------------------------------------------------------



class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer(Rewriter &R) : HandleForLabel(R), HandleForFunction(R), HandleForRecord(R) {

		
	Matcher1.addMatcher(recordDecl(hasAncestor(functionDecl())).bind("structure"),&HandleForRecord);
          Matcher1.addMatcher(functionDecl(hasDescendant(labelStmt())).bind("forFunc"),&HandleForFunction);

	  Matcher.addMatcher(functionDecl(hasDescendant(labelStmt())).bind("forFunc"),&HandleForFunction);

	 Matcher.addMatcher(labelStmt(hasParent(compoundStmt(hasParent(functionDecl())))).bind("forLabel"),&HandleForLabel);	


  }



  void HandleTranslationUnit(ASTContext &Context) override {
	  Matcher1.matchAST(Context);
    	Matcher.matchAST(Context);
  	}

	private:
		LabelHandler HandleForLabel;
		FunctionHandler HandleForFunction;
		RecordHandler HandleForRecord;
		MatchFinder Matcher, Matcher1;

};


//-------------------------------------------------------------------------------------------------------------------------------------------


class MyFrontendAction : public ASTFrontendAction {
public:
  MyFrontendAction() {}
  		void EndSourceFileAction() override 
  		{
 			TheRewriter.getEditBuffer(TheRewriter.getSourceMgr().getMainFileID()) .write(llvm::outs());
 
  		}

  		std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override 
		{

			    TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    			    return std::make_unique<MyASTConsumer>(TheRewriter);
  		}

	private:
  		Rewriter TheRewriter;
	};


//---------------------------------------------------------------------------------------------------------------------------------------------


int main(int argc, const char **argv) 

{

  CommonOptionsParser op(argc, argv, MatcherSampleCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());
  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}
