#!/usr/bin/env python3
import urllib.request
import urllib.error
from html.parser import HTMLParser
import re

class LeaderboardParser(HTMLParser):
    """Custom HTML parser to extract leaderboard data"""
    def __init__(self):
        super().__init__()
        self.in_main_row = False
        self.in_td = False
        self.td_count = 0
        self.current_row = []
        self.rows = []
        self.current_cell_data = []
        
    def handle_starttag(self, tag, attrs):
        attr_dict = dict(attrs)
        
        if tag == 'tr' and 'id' in attr_dict and attr_dict['id'].startswith('main-row-'):
            self.in_main_row = True
            self.current_row = []
            self.td_count = 0
        elif tag == 'td' and self.in_main_row:
            self.in_td = True
            self.td_count += 1
            self.current_cell_data = []
            
    def handle_endtag(self, tag):
        if tag == 'tr' and self.in_main_row:
            self.in_main_row = False
            if len(self.current_row) >= 3:
                self.rows.append(self.current_row)
        elif tag == 'td' and self.in_td:
            self.in_td = False
            # Store data for columns 2 (model), 3 (accuracy), 4 (cost)
            if self.td_count in [2, 3, 4]:
                cell_text = ' '.join(self.current_cell_data).strip()
                self.current_row.append(cell_text)
            
    def handle_data(self, data):
        if self.in_td and self.td_count in [2, 3, 4]:
            text = data.strip()
            if text:
                self.current_cell_data.append(text)

def fetch_leaderboard_data():
    """Fetch the leaderboard data from aider.chat"""
    url = "https://aider.chat/docs/leaderboards/"
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
        with urllib.request.urlopen(req) as response:
            return response.read().decode('utf-8')
    except urllib.error.URLError as e:
        raise Exception(f"Failed to fetch data: {e}")

def parse_leaderboard_html(html_content):
    """Parse the HTML content to extract leaderboard data"""
    parser = LeaderboardParser()
    parser.feed(html_content)
    
    rows = []
    for row_data in parser.rows:
        if len(row_data) >= 3:
            model_name = row_data[0]
            accuracy = row_data[1]
            cost = row_data[2]
            
            # Extract percentage from accuracy
            acc_match = re.search(r'(\d+\.?\d*)%', accuracy)
            if acc_match:
                acc_value = float(acc_match.group(1))
            else:
                continue
            
            # Extract cost value
            cost_match = re.search(r'\$(\d+\.?\d*)', cost)
            if cost_match:
                cost_value = float(cost_match.group(1))
            else:
                cost_value = None
            
            rows.append({
                'model': model_name,
                'accuracy': acc_value,
                'cost': cost_value
            })
    
    return rows

def determine_company(model_name):
    """Determine the company based on model name"""
    model_lower = model_name.lower()
    
    if 'gpt' in model_lower or 'o1' in model_lower or 'o3' in model_lower or 'o4' in model_lower or 'chatgpt' in model_lower:
        return 'OpenAI'
    elif 'claude' in model_lower:
        return 'Anthropic'
    elif 'gemini' in model_lower or 'gemma' in model_lower:
        return 'Google'
    elif 'deepseek' in model_lower:
        return 'DeepSeek'
    elif 'grok' in model_lower:
        return 'xAI'
    elif 'qwen' in model_lower or 'qwq' in model_lower:
        return 'Alibaba'
    elif 'mistral' in model_lower or 'codestral' in model_lower:
        return 'Mistral'
    elif 'yi-' in model_lower:
        return '01.AI'
    elif 'quasar' in model_lower or 'optimus' in model_lower:
        return 'OpenRouter'
    elif 'llama' in model_lower:
        return 'Meta'
    elif 'command' in model_lower:
        return 'Cohere'
    elif 'openhands' in model_lower:
        return 'AllHands'
    else:
        return 'Other'

def format_model_name(model_name):
    """Format model name for display"""
    # Remove common suffixes and clean up
    name = model_name.strip()
    
    # Common replacements
    replacements = {
        'gemini-2.5-pro-preview-06-05 (32k think)': 'Gemini 2.5 Pro 06-05 (32k)',
        'gemini-2.5-pro-preview-06-05 (default think)': 'Gemini 2.5 Pro 06-05',
        'gemini-2.5-pro-preview-05-06': 'Gemini 2.5 Pro 05-06',
        'gemini-2.5-pro-preview-03-25': 'Gemini 2.5 Pro 03-25',
        'claude-opus-4-20250514 (32k thinking)': 'claude-opus-4 (think)',
        'claude-opus-4-20250514 (no think)': 'claude-opus-4',
        'claude-3-7-sonnet-20250219 (32k thinking tokens)': 'claude-sonnet (32k)',
        'claude-3-7-sonnet-20250219 (no thinking)': 'claude-sonnet',
        'claude-sonnet-4-20250514 (32k thinking)': 'claude-sonnet-4 (32k)',
        'claude-sonnet-4-20250514 (no thinking)': 'claude-sonnet-4',
        'claude-3-5-sonnet-20241022': 'claude-3-5 sonnet',
        'claude-3-5-haiku-20241022': 'claude-haiku',
        'gemini-2.5-flash-preview-05-20 (24k think)': 'gemini-flash 05-20',
        'gemini-2.5-flash-preview-05-20 (no think)': 'gemini-flash 05-20 nt',
        'gemini-2.5-flash-preview-04-17 (default)': 'gemini-flash 04-17',
        'gemini-2.0-flash-thinking-exp-01-21': 'gemini-flash thinking',
        'gemini-2.0-flash-exp': 'gemini-flash exp',
        'DeepSeek R1 (0528)': 'DeepSeek R1',
        'DeepSeek V3 (0324)': 'DeepSeek V3 (0324)',
        'DeepSeek Chat V3 (prev)': 'DeepSeek Chat V3',
        'DeepSeek Chat V2.5': 'DeepSeek Chat V2.5',
        'DeepSeek R1 + claude-3-5-sonnet-20241022': 'DeepSeek R1+sonnet',
        'Qwen3 235B A22B diff, no think, Alibaba API': 'Qwen3 235B',
        'qwen-max-2025-01-25': 'qwen-max-2025',
        'Qwen2.5-Coder-32B-Instruct': 'Qwen Coder 32B',
        'QwQ-32B + Qwen 2.5 Coder Instruct': 'QwQ-32B+Qwen 2.5',
        'Llama 4 Maverick': 'Llama-4 Maverick',
        'command-a-03-2025-quality': 'command-a 03-25',
        'openhands-lm-32b-v0.1': 'OpenHands 32B',
        'gpt-4.5-preview': 'gpt-4.5 preview',
        'gpt-4o-2024-08-06': 'gpt-4o 2024-08-06',
        'gpt-4o-2024-11-20': 'gpt-4o 2024-11-20',
        'gpt-4o-mini-2024-07-18': 'gpt-4o mini 07-18',
        'o1-mini-2024-09-12': 'o1-mini',
        'o1-2024-12-17 (high)': 'o1 (high)',
        'chatgpt-4o-latest (2025-03-29)': 'chatgpt-4o (03-29)',
        'chatgpt-4o-latest (2025-02-15)': 'chatgpt-4o (02-15)',
        'Grok 3 Mini Beta (high)': 'Grok 3 Mini (high)',
        'Grok 3 Mini Beta (low)': 'Grok 3 Mini (low)',
        'gemini-exp-1206': 'gemini-exp-1206',
        'Gemini 2.0 Pro exp-02-05': 'Gemini 2.0 Pro 02-05',
        'gpt-4.1-mini': 'gpt-4.1 mini',
        'gpt-4.1-nano': 'gpt-4.1 nano',
        'o3 (high) + gpt-4.1': 'o3 (high)+gpt-4.1',
        'Qwen3 32B': 'Qwen3 32B',
        'Qwen2.5-Coder-32B-Instruct': 'Qwen2.5 Coder 32B',
    }
    
    return replacements.get(name, name)

def generate_javascript_rows(data):
    """Generate JavaScript rows array from parsed data"""
    js_rows = []
    
    for item in data:
        model_name = format_model_name(item['model'])
        company = determine_company(item['model'])
        
        # Format cost with appropriate decimal places
        if item['cost'] is not None:
            if item['cost'] < 1:
                cost_str = f"{item['cost']:.2f}"
            elif item['cost'] < 10:
                cost_str = f"{item['cost']:.2f}"
            elif item['cost'] < 100:
                cost_str = f"{item['cost']:.2f}"
            else:
                cost_str = f"{item['cost']:.2f}"
        else:
            cost_str = "null"
        
        # Format accuracy with 1 decimal place
        acc_str = f"{item['accuracy']:.1f}"
        
        # Calculate padding for alignment
        model_padding = 25 - len(model_name)
        model_str = f'"{model_name}"' + ' ' * max(0, model_padding)
        
        js_rows.append(f' {{model:{model_str}, acc:{acc_str}, cost:{cost_str.ljust(6)}, company:"{company}"}}')
    
    return js_rows

def update_html_file(js_rows):
    """Update the index.html file with new data"""
    with open('index.html', 'r') as f:
        html_content = f.read()
    
    # Find the rows array in the JavaScript
    pattern = r'const rows = \[(.*?)\];'
    match = re.search(pattern, html_content, re.DOTALL)
    
    if not match:
        raise ValueError("Could not find rows array in index.html")
    
    # Create new rows array
    new_rows = "const rows = [\n" + ",\n".join(js_rows) + "\n];"
    
    # Replace the old rows array with the new one
    new_html = html_content[:match.start()] + new_rows + html_content[match.end():]
    
    with open('index.html', 'w') as f:
        f.write(new_html)
    
    print(f"Updated index.html with {len(js_rows)} models")

def main():
    try:
        print("Fetching leaderboard data from https://aider.chat/docs/leaderboards/...")
        html_content = fetch_leaderboard_data()
        
        print("Parsing leaderboard data...")
        data = parse_leaderboard_html(html_content)
        
        print(f"Found {len(data)} models")
        
        if len(data) == 0:
            print("Error: No models found in the leaderboard")
            print("The website structure might have changed.")
            return 1
        
        # Sort by accuracy descending, then by cost ascending
        data.sort(key=lambda x: (-x['accuracy'], x['cost'] if x['cost'] is not None else float('inf')))
        
        print("Generating JavaScript rows...")
        js_rows = generate_javascript_rows(data)
        
        print("Updating index.html...")
        update_html_file(js_rows)
        
        print("Done! The Pareto frontier visualization has been updated.")
        
    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0

if __name__ == "__main__":
    exit(main())