package com.mistagiggles.llvm.bench;

import android.app.Activity;
import android.os.Bundle;
import android.util.Log;
import android.view.Menu;
import android.view.View;
import android.widget.Button;

public class MainActivity extends Activity {

	static final int RUNS = 10000000;
	
    static final int FACTORIAL_MAX = 12;
    
    static final int POWERS_BASE_MOD = 5;
    static final int POWERS_INDEX_MOD = 7;
    
    static final int FIB_MOD = 22;
   
    
    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.activity_main);
        
        final Button button = (Button) findViewById(R.id.button1);
        button.setOnClickListener(new View.OnClickListener() {
            public void onClick(View v) {
                // Perform action on click
            	Log.d("BENCH", "===============================================");
            	long startTime, endTime;
            	
            	startTime = System.nanoTime();
            	//FactorialSLOW();
            	//PowerSLOW();
            	//arithSLOW();
            	//testSLOW();
            	//fibbSLOW(10);
            	runFibSLOW();
            	endTime = System.nanoTime();
            	Log.d("BENCH", "MGD TEST SLOW  " + (endTime - startTime)/1000000);
            	
            	startTime = System.nanoTime();
            	//FactorialLLVM();
            	//arithLLVM();
            	//testLLVM();
            	//PowerLLVM();
            	//fibbLLVM(10);
            	runFibLLVM();
            	endTime = System.nanoTime();
            	Log.d("BENCH", "MGD TEST FAST " + (endTime - startTime)/1000000);
            	
            	startTime = System.nanoTime();
            	//FactorialJIT();
            	//PowerJIT();
            	//arithJIT();
            	//testJIT();
            	//fibbJIT(10);
            	runFibJIT();
            	endTime = System.nanoTime();
            	
            	Log.d("BENCH", "MGD TEST JIT  " + (endTime - startTime)/1000000);
            	
            	Log.d("BENCH", "===============================================");
            	
            	//Log.d("BENCH", "DONE");
            }
        });
        
        
        
        final Button button2 = (Button) findViewById(R.id.button2);
        button2.setOnClickListener(new View.OnClickListener() {
            public void onClick(View v) {
            	 Log.d("BENCH", "MGD Cleaning up");        	//}
            		finish();
            }
        });
        
       
    }
    private void FactorialLLVM()
    {
    	for(int i = 0; i < RUNS;  i++) {
    		int res = 1;
        	int j = i%FACTORIAL_MAX;
        	while(j>1) {
        		res *= j;
        		j -= 1;
        	}
        	
    	}
    }
    
    private void FactorialJIT()
    {
    	for(int i = 0; i < RUNS; i++) {
    		int res = 1;
        	int j = i%FACTORIAL_MAX;
        	while(j>1) {
        		res *= j;
        		j -= 1;
        	}
        	
    	}
    }
    
    private void FactorialSLOW()
    {
    	for(int i = 0; i < RUNS; i++) {
    		int res = 1;
        	int j = i%FACTORIAL_MAX;
        	while(j>1) {
        		res *= j;
        		j -= 1;
        	}
        	
    	}
    }

    
   
    
    private int addTwoLLVM(int a, int b)
    {
    	int[] ar = new int[4];
    	ar[0] = 1;
        ar[1] = 3;
        ar[2] = 5;
        ar[3] = 7;
      
        
        if(b > 0) {       
	    	int h;
	    	h = 5;
	    	if(h==5)
	    		return a + b;
        }
    	
    	int c = a + b;
    	int d = a * b;
    	c = c + d;
    	int e = b * a;
    	c = c - e;
    	if(c < 0)
    		return c;
    	return a+b;
    }
    
    private int factorialLLVM(int n)
    {
    	int res = 1;
    	int i = n;
    	while(i>1) {
    		res *= i;
    		i -= 1;
    	}
    	return res;
    }
    
    private int factorialSLOW(int n)
    {
    	int res = 1;
    	int i = n;
    	while(i>1) {
    		res *= i;
    		i -= 1;
    	}
    	return res;
    }
    
    private int factorialJIT(int n)
    {
    	int res = 1;
    	int i = n;
    	while(i>1) {
    		res *= i;
    		i -= 1;
    	}
    	return res;
    }
    
    private int addTwoSLOW(int a, int b)
    {
    	int[] ar = new int[4];
    	ar[0] = 1;
        ar[1] = 3;
        ar[2] = 5;
        ar[3] = 7;
      
        
        if(b > 0) {       
	    	int h;
	    	h = 5;
	    	if(h==5)
	    		return a + b;
        }
    	
    	int c = a + b;
    	int d = a * b;
    	c = c + d;
    	int e = b * a;
    	c = c - e;
    	if(c < 0)
    		return c;
    	return a+b;
    }
    
    private int arithLLVM()
    {
    	int a,b,c,d;
    	int r = 0;
    	a = b = c = d = 0;
    	for(int f = 0; f < RUNS; f++) {
	    	a = f + 5;
	    	b = f - 7;
	    	c = a+b;
	    	d = b - a;
	    	r = a+b;
	    	r = c+d;
	    	r = a+c;
	    	r = a+d;
	    	r = b+c;
	    	r = b+d;
	    	r= c+a;
	    	r=d+b;
    	}
    	return r;
    	
    }
    
    private int arithSLOW()
    {
    	int a,b,c,d;
    	int r = 0;
    	a = b = c = d = 0;
    	for(int f = 0; f < RUNS; f++) {
	    	a = f + 5;
	    	b = f - 7;
	    	c = a+b;
	    	d = b - a;
	    	r = a+b;
	    	r = c+d;
	    	r = a+c;
	    	r = a+d;
	    	r = b+c;
	    	r = b+d;
	    	r= c+a;
	    	r=d+b;
    	}
    	return r;
    	
    }
    
    private int arithJIT(int f)
    {
    	int a,b,c,d;
    	int r = 0;
    	a = b = c = d = 0;
    	
	    	a = f + 5;
	    	b = f - 7;
	    	c = a+b;
	    	d = b - a;
	    	r = a+b;
	    	r = c+d;
	    	r = a+c;
	    	r = a+d;
	    	r = b+c;
	    	r = b+d;
	    	r= c+a;
	    	r=d+b;
    	
    	return r;
    	
    }
    // n^m
    private int PowerLLVM() {
    	int res = 1;
    	for(int f = 0; f < RUNS; f++) {
	    	
	    	int m = f % POWERS_BASE_MOD;
	    	int n = f % POWERS_INDEX_MOD;
	    	for(int i = 0; i < m; i++) {
	    		res *= n;
	    	}
    	}
    	return res;
    }
    
    private int PowerSLOW() {
    	int res = 1;
    	for(int f = 0; f < RUNS; f++) {
	    	
	    	int m = f % POWERS_BASE_MOD;
	    	int n = f % POWERS_INDEX_MOD;
	    	for(int i = 0; i < m; i++) {
	    		res *= n;
	    	}
    	}
    	return res;
    }
    
    private int PowerJIT() {
    	int res = 1;
    	for(int f = 0; f < RUNS; f++) {
	    	
	    	int m = f % POWERS_BASE_MOD;
	    	int n = f % POWERS_INDEX_MOD;
	    	for(int i = 0; i < m; i++) {
	    		res *= n;
	    	}
    	}
    	return res;
    }
    
    private int testJIT() {
    	int k = 0;
    	for(int i = 0; i < 10000; i++) {
    		for(int j = 0; j < 10000; j++) {
    			k += i*j;
    		}
    	}
    	return k;
    }
    
    private int testLLVM() {
    	int k = 0;
    	for(int i = 0; i < 10000; i++) {
    		for(int j = 0; j < 10000; j++) {
    			k += i*j;
    		}
    	}
    	return k;
    }
    
    private int testSLOW() {
    	int k = 0;
    	for(int i = 0; i < 10000; i++) {
    		for(int j = 0; j < 10000; j++) {
    			k += i*j;
    		}
    	}
    	return k;
    }
    
    private int fibbLLVM(int t){
    	int a = 0;
    	int b = 1;
    	int c = a+b;
    	if(t==0){return a;}
    	if(t==1){return b;}
    	for(int i = 1; i < t; i++) {
    		c = a + b;
    		a = b;
    		b = c;
    	}
    	return c;
    }
    
    private int fibbJIT(int t){
    	int a = 0;
    	int b = 1;
    	int c = a+b;
    	if(t==0){return a;}
    	if(t==1){return b;}
    	for(int i = 1; i < t; i++) {
    		c = a + b;
    		a = b;
    		b = c;
    	}
    	return c;
    }
    
    private int fibbSLOW(int t){
    	int a = 0;
    	int b = 1;
    	int c = a+b;
    	if(t==0){return a;}
    	if(t==1){return b;}
    	for(int i = 1; i < t; i++) {
    		c = a + b;
    		a = b;
    		b = c;
    	}
    	return c;
    }
    
    private void runFibLLVM() {
    	for(int i = 0; i < RUNS; i++) {
    		fibbLLVM(i%FIB_MOD);
    	}
    }
    
    private void runFibSLOW() {
    	for(int i = 0; i < RUNS; i++) {
    		fibbSLOW(i%FIB_MOD);
    	}
    }
    
    private void runFibJIT() {
    	for(int i = 0; i < RUNS; i++) {
    		fibbJIT(i%FIB_MOD);
    	}
    }
    
    
    
    
    
    
    @Override
    public boolean onCreateOptionsMenu(Menu menu) {
        // Inflate the menu; this adds items to the action bar if it is present.
        getMenuInflater().inflate(R.menu.activity_main, menu);
        return true;
    }
    
    public void onDestroy() {
        super.onDestroy();
        android.os.Process.killProcess(android.os.Process.myPid());
    }     
    
}
